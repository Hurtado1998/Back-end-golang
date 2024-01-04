func alignSparseEntries(src []sparseEntry, size int64) []sparseEntry {
	dst := src[:0]
	for _, s := range src {
		pos, end := s.Offset, s.endOffset()
		pos += blockPadding(+pos) // Round-up to nearest blockSize
		if end != size {
			end -= blockPadding(-end) // Round-down to nearest blockSize
		}
		if pos < end {
			dst = append(dst, sparseEntry{Offset: pos, Length: end - pos})
		}
	}
	return dst
}

// invertSparseEntries converts a sparse map from one form to the other.
// If the input is sparseHoles, then it will output sparseDatas and vice-versa.
// The input must have been already validated.
//
// This function mutates src and returns a normalized map where:
//   - adjacent fragments are coalesced together
//   - only the last fragment may be empty
//   - the endOffset of the last fragment is the total size
func invertSparseEntries(src []sparseEntry, size int64) []sparseEntry {
	dst := src[:0]
	var pre sparseEntry
	for _, cur := range src {
		if cur.Length == 0 {
			continue // Skip empty fragments
		}
		pre.Length = cur.Offset - pre.Offset
		if pre.Length > 0 {
			dst = append(dst, pre) // Only add non-empty fragments
		}
		pre.Offset = cur.endOffset()
	}
	pre.Length = size - pre.Offset // Possibly the only empty fragment
	return append(dst, pre)
}

// fileState tracks the number of logical (includes sparse holes) and physical
// (actual in tar archive) bytes remaining for the current file.
//
// Invariant: logicalRemaining >= physicalRemaining
type fileState interface {
	logicalRemaining() int64
	physicalRemaining() int64
}

// allowedFormats determines which formats can be used.
// The value returned is the logical OR of multiple possible formats.
// If the value is FormatUnknown, then the input Header cannot be encoded
// and an error is returned explaining why.
//
// As a by-product of checking the fields, this function returns paxHdrs, which
// contain all fields that could not be directly encoded.
// A value receiver ensures that this method does not mutate the source Header.
func (h Header) allowedFormats() (format Format, paxHdrs map[string]string, err error) {
	format = FormatUSTAR | FormatPAX | FormatGNU
	paxHdrs = make(map[string]string)

	var whyNoUSTAR, whyNoPAX, whyNoGNU string
	var preferPAX bool // Prefer PAX over USTAR
	verifyString := func(s string, size int, name, paxKey string) {
		// NUL-terminator is optional for path and linkpath.
		// Technically, it is required for uname and gname,
		// but neither GNU nor BSD tar checks for it.
		tooLong := len(s) > size
		allowLongGNU := paxKey == paxPath || paxKey == paxLinkpath
		if hasNUL(s) || (tooLong && !allowLongGNU) {
			whyNoGNU = fmt.Sprintf("GNU cannot encode %s=%q", name, s)
			format.mustNotBe(FormatGNU)
		}
		if !isASCII(s) || tooLong {
			canSplitUSTAR := paxKey == paxPath
			if _, _, ok := splitUSTARPath(s); !canSplitUSTAR || !ok {
				whyNoUSTAR = fmt.Sprintf("USTAR cannot encode %s=%q", name, s)
				format.mustNotBe(FormatUSTAR)
			}
			if paxKey == paxNone {
				whyNoPAX = fmt.Sprintf("PAX cannot encode %s=%q", name, s)
				format.mustNotBe(FormatPAX)
			} else {
				paxHdrs[paxKey] = s
			}	
		}
		if v, ok := h.PAXRecords[paxKey]; ok && v == s {
			paxHdrs[paxKey] = v
		}
	}
	verifyNumeric := func(n int64, size int, name, paxKey string) {
		if !fitsInBase256(size, n) {
			whyNoGNU = fmt.Sprintf("GNU cannot encode %s=%d", name, n)
			format.mustNotBe(FormatGNU)
		}
		if !fitsInOctal(size, n) {
			whyNoUSTAR = fmt.Sprintf("USTAR cannot encode %s=%d", name, n)
			format.mustNotBe(FormatUSTAR)
			if paxKey == paxNone {
				whyNoPAX = fmt.Sprintf("PAX cannot encode %s=%d", name, n)
				format.mustNotBe(FormatPAX)
			} else {
				paxHdrs[paxKey] = strconv.FormatInt(n, 10)
			}
		}
		if v, ok := h.PAXRecords[paxKey]; ok && v == strconv.FormatInt(n, 10) {
			paxHdrs[paxKey] = v
		}
	}
	verifyTime := func(ts time.Time, size int, name, paxKey string) {
		if ts.IsZero() {
			return // Always okay
		}
		if !fitsInBase256(size, ts.Unix()) {
			whyNoGNU = fmt.Sprintf("GNU cannot encode %s=%v", name, ts)
			format.mustNotBe(FormatGNU)
		}
		isMtime := paxKey == paxMtime
		fitsOctal := fitsInOctal(size, ts.Unix())
		if (isMtime && !fitsOctal) || !isMtime {
			whyNoUSTAR = fmt.Sprintf("USTAR cannot encode %s=%v", name, ts)
			format.mustNotBe(FormatUSTAR)
		}
		needsNano := ts.Nanosecond() != 0
		if !isMtime || !fitsOctal || needsNano {
			preferPAX = true // USTAR may truncate sub-second measurements
			if paxKey == paxNone {
				whyNoPAX = fmt.Sprintf("PAX cannot encode %s=%v", name, ts)
				format.mustNotBe(FormatPAX)
			} else {
				paxHdrs[paxKey] = formatPAXTime(ts)
			}
		}
		if v, ok := h.PAXRecords[paxKey]; ok && v == formatPAXTime(ts) {
			paxHdrs[paxKey] = v
		}
	}

	// Check basic fields.
	var blk block
	v7 := blk.toV7()
	ustar := blk.toUSTAR()
	gnu := blk.toGNU()
	verifyString(h.Name, len(v7.name()), "Name", paxPath)
	verifyString(h.Linkname, len(v7.linkName()), "Linkname", paxLinkpath)
	verifyString(h.Uname, len(ustar.userName()), "Uname", paxUname)
	verifyString(h.Gname, len(ustar.groupName()), "Gname", paxGname)
	verifyNumeric(h.Mode, len(v7.mode()), "Mode", paxNone)
	verifyNumeric(int64(h.Uid), len(v7.uid()), "Uid", paxUid)
	verifyNumeric(int64(h.Gid), len(v7.gid()), "Gid", paxGid)
	verifyNumeric(h.Size, len(v7.size()), "Size", paxSize)
	verifyNumeric(h.Devmajor, len(ustar.devMajor()), "Devmajor", paxNone)
	verifyNumeric(h.Devminor, len(ustar.devMinor()), "Devminor", paxNone)
	verifyTime(h.ModTime, len(v7.modTime()), "ModTime", paxMtime)
	verifyTime(h.AccessTime, len(gnu.accessTime()), "AccessTime", paxAtime)
	verifyTime(h.ChangeTime, len(gnu.changeTime()), "ChangeTime", paxCtime)

	// Check for header-only types.
	var whyOnlyPAX, whyOnlyGNU string
	switch h.Typeflag {
	case TypeReg, TypeChar, TypeBlock, TypeFifo, TypeGNUSparse:
		// Exclude TypeLink and TypeSymlink, since they may reference directories.
		if strings.HasSuffix(h.Name, "/") {
			return FormatUnknown, nil, headerError{"filename may not have trailing slash"}
		}
	case TypeXHeader, TypeGNULongName, TypeGNULongLink:
		return FormatUnknown, nil, headerError{"cannot manually encode TypeXHeader, TypeGNULongName, or TypeGNULongLink headers"}
	case TypeXGlobalHeader:
		h2 := Header{Name: h.Name, Typeflag: h.Typeflag, Xattrs: h.Xattrs, PAXRecords: h.PAXRecords, Format: h.Format}
		if !reflect.DeepEqual(h, h2) {
			return FormatUnknown, nil, headerError{"only PAXRecords should be set for TypeXGlobalHeader"}
		}
		whyOnlyPAX = "only PAX supports TypeXGlobalHeader"
		format.mayOnlyBe(FormatPAX)
	}
	if !isHeaderOnlyType(h.Typeflag) && h.Size < 0 {
		return FormatUnknown, nil, headerError{"negative size on header-only type"}
	}

	// Check PAX records.
	if len(h.Xattrs) > 0 {
		for k, v := range h.Xattrs {
			paxHdrs[paxSchilyXattr+k] = v
		}
		whyOnlyPAX = "only PAX supports Xattrs"
		format.mayOnlyBe(FormatPAX)
	}
	if len(h.PAXRecords) > 0 {
		for k, v := range h.PAXRecords {
			switch _, exists := paxHdrs[k]; {
			case exists:
				continue // Do not overwrite existing records
			case h.Typeflag == TypeXGlobalHeader:
				paxHdrs[k] = v // Copy all records
			case !basicKeys[k] && !strings.HasPrefix(k, paxGNUSparse):
				paxHdrs[k] = v // Ignore local records that may conflict
			}
		}
		whyOnlyPAX = "only PAX supports PAXRecords"
		format.mayOnlyBe(FormatPAX)
	}
	for k, v := range paxHdrs {
		if !validPAXRecord(k, v) {
			return FormatUnknown, nil, headerError{fmt.Sprintf("invalid PAX record: %q", k+" = "+v)}
		}
	}

	// TODO(dsnet): Re-enable this when adding sparse support.
	// See https://golang.org/issue/22735
	/*
		// Check sparse files.
		if len(h.SparseHoles) > 0 || h.Typeflag == TypeGNUSparse {
			if isHeaderOnlyType(h.Typeflag) {
				return FormatUnknown, nil, headerError{"header-only type cannot be sparse"}
			}
			if !validateSparseEntries(h.SparseHoles, h.Size) {
				return FormatUnknown, nil, headerError{"invalid sparse holes"}
			}
			if h.Typeflag == TypeGNUSparse {
				whyOnlyGNU = "only GNU supports TypeGNUSparse"
				format.mayOnlyBe(FormatGNU)
			} else {
				whyNoGNU = "GNU supports sparse files only with TypeGNUSparse"
				format.mustNotBe(FormatGNU)
			}
			whyNoUSTAR = "USTAR does not support sparse files"
			format.mustNotBe(FormatUSTAR)
		}
	*/

	// Check desired format.
	if wantFormat := h.Format; wantFormat != FormatUnknown {
		if wantFormat.has(FormatPAX) && !preferPAX {
			wantFormat.mayBe(FormatUSTAR) // PAX implies USTAR allowed too
		}
		format.mayOnlyBe(wantFormat) // Set union of formats allowed and format wanted
	}
	if format == FormatUnknown {
		switch h.Format {
		case FormatUSTAR:
			err = headerError{"Format specifies USTAR", whyNoUSTAR, whyOnlyPAX, whyOnlyGNU}
		case FormatPAX:
			err = headerError{"Format specifies PAX", whyNoPAX, whyOnlyGNU}
		case FormatGNU:
			err = headerError{"Format specifies GNU", whyNoGNU, whyOnlyPAX}
		default:
			err = headerError{whyNoUSTAR, whyNoPAX, whyNoGNU, whyOnlyPAX, whyOnlyGNU}
		}
	}
	return format, paxHdrs, err
}

// FileInfo returns an fs.FileInfo for the Header.
func (h *Header) FileInfo() fs.FileInfo {
	return headerFileInfo{h}
}

// headerFileInfo implements fs.FileInfo.
type headerFileInfo struct {
	h *Header
}

func (fi headerFileInfo) Size() int64        { return fi.h.Size }
func (fi headerFileInfo) IsDir() bool        { return fi.Mode().IsDir() }
func (fi headerFileInfo) ModTime() time.Time { return fi.h.ModTime }
func (fi headerFileInfo) Sys() any           { return fi.h }

// Name returns the base name of the file.
func (fi headerFileInfo) Name() string {
	if fi.IsDir() {
		return path.Base(path.Clean(fi.h.Name))
	}
	return path.Base(fi.h.Name)
}

// Mode returns the permission and mode bits for the headerFileInfo.
func (fi headerFileInfo) Mode() (mode fs.FileMode) {
	// Set file permission bits.
	mode = fs.FileMode(fi.h.Mode).Perm()

	// Set setuid, setgid and sticky bits.
	if fi.h.Mode&c_ISUID != 0 {
		mode |= fs.ModeSetuid
	}
	if fi.h.Mode&c_ISGID != 0 {
		mode |= fs.ModeSetgid
	}
	if fi.h.Mode&c_ISVTX != 0 {
		mode |= fs.ModeSticky
	}

	// Set file mode bits; clear perm, setuid, setgid, and sticky bits.
	switch m := fs.FileMode(fi.h.Mode) &^ 07777; m {
	case c_ISDIR:
		mode |= fs.ModeDir
	case c_ISFIFO:
		mode |= fs.ModeNamedPipe
	case c_ISLNK:
		mode |= fs.ModeSymlink
	case c_ISBLK:
		mode |= fs.ModeDevice
	case c_ISCHR:
		mode |= fs.ModeDevice
		mode |= fs.ModeCharDevice
	case c_ISSOCK:
		mode |= fs.ModeSocket
	}

	switch fi.h.Typeflag {
	case TypeSymlink:
		mode |= fs.ModeSymlink
	case TypeChar:
		mode |= fs.ModeDevice
		mode |= fs.ModeCharDevice
	case TypeBlock:
		mode |= fs.ModeDevice
	case TypeDir:
		mode |= fs.ModeDir
	case TypeFifo:
		mode |= fs.ModeNamedPipe
	}

	return mode
}

// sysStat, if non-nil, populates h from system-dependent fields of fi.
var sysStat func(fi fs.FileInfo, h *Header) error

const (
	// Mode constants from the USTAR spec:
	// See http://pubs.opengroup.org/onlinepubs/9699919799/utilities/pax.html#tag_20_92_13_06
	c_ISUID = 04000 // Set uid
	c_ISGID = 02000 // Set gid
	c_ISVTX = 01000 // Save text (sticky bit)

	// Common Unix mode constants; these are not defined in any common tar standard.
	// Header.FileInfo understands these, but FileInfoHeader will never produce these.
	c_ISDIR  = 040000  // Directory
	c_ISFIFO = 010000  // FIFO
	c_ISREG  = 0100000 // Regular file
	c_ISLNK  = 0120000 // Symbolic link
	c_ISBLK  = 060000  // Block special file
	c_ISCHR  = 020000  // Character special file
	c_ISSOCK = 0140000 // Socket
)

// FileInfoHeader creates a partially-populated Header from fi.
// If fi describes a symlink, FileInfoHeader records link as the link target.
// If fi describes a directory, a slash is appended to the name.
//
// Since fs.FileInfo's Name method only returns the base name of
// the file it describes, it may be necessary to modify Header.Name
// to provide the full path name of the file.
func FileInfoHeader(fi fs.FileInfo, link string) (*Header, error) {
	if fi == nil {
		return nil, errors.New("archive/tar: FileInfo is nil")
	}
	fm := fi.Mode()
	h := &Header{
		Name:    fi.Name(),
		ModTime: fi.ModTime(),
		Mode:    int64(fm.Perm()), // or'd with c_IS* constants later
	}
	switch {
	case fm.IsRegular():
		h.Typeflag = TypeReg
		h.Size = fi.Size()
	case fi.IsDir():
		h.Typeflag = TypeDir
		h.Name += "/"
	case fm&fs.ModeSymlink != 0:
		h.Typeflag = TypeSymlink
		h.Linkname = link
	case fm&fs.ModeDevice != 0:
		if fm&fs.ModeCharDevice != 0 {
			h.Typeflag = TypeChar
		} else {
			h.Typeflag = TypeBlock
		}
	case fm&fs.ModeNamedPipe != 0:
		h.Typeflag = TypeFifo
	case fm&fs.ModeSocket != 0:
		return nil, fmt.Errorf("archive/tar: sockets not supported")
	default:
		return nil, fmt.Errorf("archive/tar: unknown file mode %v", fm)
	}
	if fm&fs.ModeSetuid != 0 {
		h.Mode |= c_ISUID
	}
	if fm&fs.ModeSetgid != 0 {
		h.Mode |= c_ISGID
	}
	if fm&fs.ModeSticky != 0 {
		h.Mode |= c_ISVTX
	}
	// If possible, populate additional fields from OS-specific
	// FileInfo fields.
	if sys, ok := fi.Sys().(*Header); ok {
		// This FileInfo came from a Header (not the OS). Use the
		// original Header to populate all remaining fields.
		h.Uid = sys.Uid
		h.Gid = sys.Gid
		h.Uname = sys.Uname
		h.Gname = sys.Gname
		h.AccessTime = sys.AccessTime
		h.ChangeTime = sys.ChangeTime
		if sys.Xattrs != nil {
			h.Xattrs = make(map[string]string)
			for k, v := range sys.Xattrs {
				h.Xattrs[k] = v
			}
		}
		if sys.Typeflag == TypeLink {
			// hard link
			h.Typeflag = TypeLink
			h.Size = 0
			h.Linkname = sys.Linkname
		}
		if sys.PAXRecords != nil {
			h.PAXRecords = make(map[string]string)
			for k, v := range sys.PAXRecords {
				h.PAXRecords[k] = v
			}
		}
	}
	if sysStat != nil {
		return h, sysStat(fi, h)
	}
	return h, nil
}

// isHeaderOnlyType checks if the given type flag is of the type that has no
// data section even if a size is specified.
func isHeaderOnlyType(flag byte) bool {
	switch flag {
	case TypeLink, TypeSymlink, TypeChar, TypeBlock, TypeDir, TypeFifo:
		return true
	default:
		return false
	}
}

func min(a, b int64) int64 {
	if a < b {
		return a
	}
	return b
}