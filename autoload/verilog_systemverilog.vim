" Verilog/SystemVerilog support functions
" Language:     Verilog/SystemVerilog
" Maintainer:   Vitor Antunes <vitor.hda@gmail.com>

"------------------------------------------------------------------------
" Omni completion functions
"
" Requires ctags from:
" https://github.com/fishman/ctags
" https://github.com/exuberant-ctags/ctags
" ctags must be run with --extra=+q
" {{{
function! verilog_systemverilog#Complete(findstart, base)
  "------------------------------------------------------------------------
  " Phase 1: Find and return prefix of completion
  if a:findstart
    let linenr = line('.')
    let line = getline('.')
    let start = col('.')
    let prefixpos = -1
    let s:instname = ''
    let s:insttype = ''

    " Define start position depending on relation with end of line
    if start == col('$')
      let wordpos = start
    else
      let wordpos = start - 1
    endif

    " Search for keywords in line
    while start > 0
      if line[start - 1] == ']'
        " Skip over [...]
        while start > 0
          let start -= 1
          if line[start - 1] == '['
            break
          endif
        endwhile
      else
        if line[start - 1] == '.'
          " Found separator
          let prefixpos = start
        elseif prefixpos >= 0 && line[start - 1] =~ '\(\s\|(\)'
          " Stop when a whitespace or an open parentheses are found
          break
        endif
      endif

      let start -= 1
    endwhile

    " Determine prefix word
    if prefixpos >= 0
      let s:prefix = strpart(line, start, prefixpos - start)
      let s:word = strpart(line, prefixpos, wordpos - prefixpos)

      if s:prefix == '.'
        " Get instance info and break from while loop
        let values = s:GetInstanceInfo(linenr, start)
        let s:instname = values[0]
        let s:insttype = values[1]
      endif
    endif

    return prefixpos
  endif

  "------------------------------------------------------------------------
  " Phase 2: Search for type definition in tags file
  if exists("s:prefix") && s:prefix != ''
    call verilog_systemverilog#Verbose("Prefix: " . s:prefix)
    call verilog_systemverilog#Verbose("Word  : " . s:word)
    if s:insttype != ''
      " Process an instance
      call verilog_systemverilog#Verbose("Process instance")
      if exists("s:word")
        let tags = taglist('^' . s:insttype . '\.' . s:word)
      else
        let tags = taglist('^' . s:insttype . '\.')
      endif
      call verilog_systemverilog#Verbose("Number of tags found: " . len(tags))
      if s:instname != ''
        " In instances only return ports
        let tags = s:FilterPorts(tags)
        " Filter out hierarchical ports
        call filter(tags, 'len(split(v:val["name"], "\\.")) > 2 ? 0 : 1')
        call verilog_systemverilog#Verbose("Number of tags after filtering: " . len(tags))
        " Remove the module name prefix
        call map(tags, 'strpart(v:val["name"], len(s:insttype . "."))')
        if (v:version >= 704)
          return {'words' : tags}
        else
          return tags
        endif
      else
        " In parameter list only return constants
        let tags = s:FilterConstants(tags)
        " Filter out hierarchical ports
        call filter(tags, 'len(split(v:val["name"], "\\.")) > 2 ? 0 : 1')
        call verilog_systemverilog#Verbose("Number of tags after filtering: " . len(tags))
        " Remove the module name prefix
        call map(tags, 'strpart(v:val["name"], len(s:insttype . "."))')
        if (v:version >= 704)
          return {'words' : tags}
        else
          return tags
        endif
      endif
    elseif s:instname != ''
      " Process a function/task call
      call verilog_systemverilog#Verbose("Searching for function")
      let items = split(s:instname, '\.')
      if len(items) > 1
        let word_list = [s:GetVariableType(items[0])]
        call extend(word_list, items[1:])
        let base = join(word_list, ".")
      elseif len(items) == 1
        let base = s:instname
      endif
      call verilog_systemverilog#Verbose("Searching tags starting with " . base)
      let tags = s:FilterPortsOrConstants(taglist('^' . base . '\.'))
      call map(tags, 'strpart(v:val["name"], len(base . "."))')
      if (v:version >= 704)
        return {'words' : tags}
      else
        return tags
      endif
    else
      " Process an object
      call verilog_systemverilog#Verbose("Process object")
      let idx = match(s:prefix, '\.')
      if idx >= 0
        let object = strpart(s:prefix, 0, idx)
      else
        let object = s:prefix
      endif

      let type = s:GetVariableType(object)
      if type != ""
        " Check if this is a class defined type
        let newtype = s:GetClassDefaultParameterValue("", type)
        if newtype != ""
          let type = newtype
        endif
        " Search for inherited tags
        let tags = s:GetInheritanceTags(type, object)
        call verilog_systemverilog#Verbose("Searching tags starting with " . type)
        let localtags = taglist('^' . type . '\.' . s:word)
        let localtags = s:AppendSignature(localtags)
        " Filter out parameters
        call filter(localtags, 'v:val["kind"] != "c"')
        " Remove the variable type prefix
        call map(localtags, 'strpart(v:val["name"], len(type)+1)')
        let tags += localtags
        " Break if no tags were found
        if len(tags) == 0
          return -1
        endif
        " Filter out hierarchical ports
        call filter(tags, 'len(split(v:val, "\\.")) > 1 ? 0 : 1')
        if (v:version >= 704)
          return {'words' : tags}
        else
          return tags
        endif
      endif
      return -1
    endif
  else
    return -1
  endif
endfunction

" Search file for instance information:
" * name
" * type (typically a module name, but can also be a function/task/etc)
" * line number
function! s:GetInstanceInfo(linenr, column)
  let linenr = a:linenr
  let line = getline(linenr)
  let start = a:column
  let instname = ""
  let insttype = ""
  let ininstdecl = 0
  let ininsttype = 0
  let p = 0
  let b = 0

  call verilog_systemverilog#Verbose("Searching for instance info, starting on line " . linenr)
  while linenr > 0
    while start > 0
      " Give up if a ; is found.
      if line[start - 1] == ';'
        call verilog_systemverilog#Verbose("Giving up instance info search, on line " . linenr)
        break
      " Skip over (...)
      elseif line[start - 1] == ')' || p > 0
        if line[start - 1] == ')'
          call verilog_systemverilog#Verbose("Skipping parentheses, started on line " . linenr)
        endif
        while start > 0
          if line[start - 1] == ')'
            let p += 1
          elseif line[start - 1] == '('
            let p -= 1
            if p == 0
              call verilog_systemverilog#Verbose("Skipping parentheses, ended on line " . linenr)
              break
            endif
          endif
          let start -= 1
        endwhile
      " Skip over [...]
      elseif line[start - 1] == ']' || b > 0
        if line[start - 1] == ']'
          call verilog_systemverilog#Verbose("Skipping brackets, started on line " . linenr)
        endif
        while start > 0
          if line[start - 1] == ']'
            let b += 1
          elseif line[start - 1] == '['
            let b -= 1
            if b == 0
              call verilog_systemverilog#Verbose("Skipping brackets, ended on line " . linenr)
              break
            endif
          endif
          let start -= 1
        endwhile
      " An unmatched opening parentheses indicate start of instance
      " From here backward search for the instance declaration
      elseif line[start - 1] == '(' && p == 0
        if line[start - 2] == '#'
          let ininsttype = -1
          call verilog_systemverilog#Verbose("Found instance parameter declaration on line " . linenr)
        else
          let ininstdecl = -1
          call verilog_systemverilog#Verbose("Found instance declaration name start, on line " . linenr)
        endif
      elseif ininstdecl < 0 && line[start - 1] =~ '\w'
        let ininstdecl = start
      elseif ininstdecl > 0 && ininsttype == 0 && (line[start - 1] =~ '\s' || start == 1)
        if start == 1 && line[start - 1] !~ '\s'
          let instname = strpart(line, 0, ininstdecl)
        else
          let instname = strpart(line, start, ininstdecl - start)
        endif
        call verilog_systemverilog#Verbose("Found instance name \"" . instname . "\", on line " . linenr)
        let ininsttype = -1
      elseif ininsttype < 0 && line[start - 1] =~ '\w'
        let ininsttype = start
      elseif ininsttype > 0 && (line[start - 1] =~ '\s' || start == 1)
        if start == 1 && line[start - 1] !~ '\s'
          let insttype = strpart(line, 0, ininsttype)
        else
          let insttype = strpart(line, start, ininsttype - start)
        endif
        call verilog_systemverilog#Verbose("Found instance type \"" . insttype . "\", on line " . linenr)
        break
      endif

      let start -= 1
    endwhile

    " Break search when instance type is found
    if ininsttype > 0
      break
    endif

    " Give up if a ; is found.
    if line[start - 1] == ';'
      call verilog_systemverilog#Verbose("Giving up instance info search, on line " . linenr)
      break
    endif

    " Check next line
    let linenr -= 1
    let line = getline(linenr)
    let start = len(line)
  endwhile

  call verilog_systemverilog#Verbose("Found instance. Name: »" . instname . "« Type: »" . insttype . "«")
  return [instname, insttype, linenr]
endfunction

" Append signature to functions and tasks
function s:AppendSignature(tags)
  let newtags = []
  for t in a:tags
    if t["kind"] == "t" || t["kind"] == "f"
      let t["name"] = t["name"] . "()"
    endif
    call add(newtags, t)
  endfor
  return newtags
endfunction

" Get list of inheritance tags
function s:GetInheritanceTags(class, object)
  call verilog_systemverilog#Verbose("Searching inheritance of " . a:object)
  let tags = []
  let inheritance = a:class
  let classtag = taglist('^' . inheritance . '$')
  while exists('classtag[0]["inherits"]')
    call verilog_systemverilog#Verbose("Following class " . a:class)
    call verilog_systemverilog#Verbose(inheritance . " inherits " . classtag[0]["inherits"])
    let inheritance = classtag[0]["inherits"]
    " First check if inheritance is a parameter of the class
    let localtags = taglist('^' . a:class . '.' . inheritance . '$')
    if len(localtags) == 1 && localtags[0]["kind"] == "c"
      call verilog_systemverilog#Verbose(a:class . " inherits from a parameter")
      let parameter = inheritance
      " Search for parameter initialization in object declaration line
      let inheritance = s:GetObjectParameterValue(a:object, parameter)
      if inheritance == ""
        " Search for parameter default value in class declaration
        let inheritance = s:GetClassDefaultParameterValue(a:class, parameter)
        if inheritance == ""
          call verilog_systemverilog#Verbose("No default inheritance found")
          return tags
        endif
      endif
      call verilog_systemverilog#Verbose(a:class . " inherits from " . inheritance)
    endif
    " Get tags from inherited class
    let localtags = taglist('^' . inheritance . '.' . s:word)
    let localtags = s:AppendSignature(localtags)
    call map(localtags, 'strpart(v:val["name"], len(inheritance)+1)')
    let tags += localtags
    let classtag = taglist('^' . inheritance . '$')
  endwhile
  return tags
endfunction

" Searches for declaration of "word" and returns its type
function s:GetVariableType(word)
  let position = getpos(".")
  if searchdecl(a:word, 0) == 0
    let line = getline('.')
    let line = substitute(line, '\v^\s*(const|rand|randc)', '', '')
    let line = substitute(line, '\v^\s*(static|protected|local)', '', '')
    let type = split(line)[0]
    call verilog_systemverilog#Verbose("Found declation for: " . a:word . " (" . type . ")")
    call setpos(".", position)
    return type
  endif
  return 0
endfunction

" Searches for declaration of "object" and returns "parameter" initialization value
function s:GetObjectParameterValue(object, parameter)
  let position = getpos(".")
  if searchdecl(a:object, 0) == 0
    let line = getline('.')
    if match(line, 'type\s\+' . a:parameter . '\s*=\s*\w\+') >= 0
      let value = substitute(line, '.*\<type\s\+' . a:parameter . '\s*=\s*\(\w\+\).*', '\1', '')
      " TODO If type was not found search in the previous line
      call verilog_systemverilog#Verbose("Found variable initialization value: " . a:parameter . " = " . value)
      call setpos(".", position)
      return value
    endif
  endif
  call verilog_systemverilog#Verbose("Initialization of " . a:parameter . " was not found in " . a:object . " declaration")
  call setpos(".", position)
  return ""
endfunction

" Searches for declaration of "class" and returns default "parameter" value
function s:GetClassDefaultParameterValue(class, parameter)
  if a:class == ""
    call verilog_systemverilog#Verbose("Search for default value of parameter " . a:parameter . " in current class")
    let declaration = {'cmd': '/.*type\s\+' . a:parameter . '\s*='}
    let contents = readfile(@%)
  else
    call verilog_systemverilog#Verbose("Search for default value of parameter " . a:parameter . " of class " . a:class)
    let declaration = taglist('^' . a:class . '$')[0]
    let contents = readfile(declaration.filename)
  endif
  if declaration.cmd[0] == '/'
    " Find index through pattern
    let pattern = strpart(declaration.cmd, 1, len(declaration.cmd) - 2)
    let match_idx = match(contents, pattern)
  else
    " Calculate index from line number
    let match_idx = declaration.cmd - 1
  endif
  if match_idx >= 0
    " Search for parameter in class declaration
    while match_idx < len(contents) && contents[match_idx] !~ ';' && contents[match_idx] !~ a:parameter
      let match_idx += 1
    endwhile
    if contents[match_idx] !~ a:parameter
      call verilog_systemverilog#Verbose("No declaration of " . a:parameter . " was found in class " . a:class)
      return ""
    endif
    " Find value assignment in current line
    let pattern = 'type\s\+' . a:parameter . '\s*=\s*\w\+'
    let idx_start = match(contents[match_idx], pattern)
    if idx_start >= 0
      let idx_end = matchend(contents[match_idx], pattern) - 1
      let result = contents[match_idx][idx_start : idx_end]
      let result = substitute(split(result, '=')[1], '^\s*\(.\{-\}\)\(\s\|,\)*$', '\1', '')
      return result
    else
      call verilog_systemverilog#Verbose("Found parameter " . a:parameter . "but failed to find assignment in the same line")
      return ""
    endif
  else
    call verilog_systemverilog#Verbose("Parameter default value not found")
    return ""
  endif
endfunction

" Filter tag list to only return ports
function s:FilterPorts(tags)
  let tags = a:tags
  call filter(tags, 'has_key(v:val, "kind") ? v:val["kind"] == "p" : 1')
  return tags
endfunction

" Filter tag list to only return constants
function s:FilterConstants(tags)
  let tags = a:tags
  call filter(tags, 'has_key(v:val, "kind") ? v:val["kind"] == "c" : 1')
  return tags
endfunction

" Filter tag list to only return ports or constants
function s:FilterPortsOrConstants(tags)
  let tags = a:tags
  call filter(tags, 'has_key(v:val, "kind") ? v:val["kind"] == "p" || v:val["kind"] == "c" : 1')
  return tags
endfunction
" }}}

"------------------------------------------------------------------------
" Common functions
" {{{
" Verbose messaging
" Only displays messages if b:verilog_verbose or g:verilog_verbose is defined
function verilog_systemverilog#Verbose(message)
  if exists("b:verilog_verbose") || exists("g:verilog_verbose")
    echom a:message
  endif
endfunction
" }}}

"------------------------------------------------------------------------
" External functions
" {{{
function verilog_systemverilog#GotoInstanceStart(line, column)
  let values = s:GetInstanceInfo(a:line, col('$'))
  if values[2] != ""
    call cursor(values[2], a:column)
  endif
endfunction

function verilog_systemverilog#FollowInstanceTag(line, column)
  let values = s:GetInstanceInfo(a:line, col('$'))
  if values[1] != ""
    execute "tag " . values[1]
  endif
endfunction

function verilog_systemverilog#FollowInstanceSearchWord(line, column)
  let @/='\<'.expand("<cword>").'\>'
  call verilog_systemverilog#FollowInstanceTag(a:line, a:column)
  exec "normal /" . @/
  normal n
endfunction
" }}}

"------------------------------------------------------------------------
" Definitions for errorformat
" {{{ 
function! verilog_systemverilog#VerilogErrorFormat(...)
  " Choose tool
  if (a:0 == 0)
    let l:tool = inputlist([
          \"1. VCS",
          \"2. Modelsim",
          \"3. iverilog",
          \"4. cver",
          \"5. Leda",
          \"6. NCVerilog",
          \])
    echo "\n"
    if (l:tool == 1)
      let l:tool = "vcs"
    elseif (l:tool == 2)
      let l:tool = "msim"
    elseif (l:tool == 3)
      let l:tool = "iverilog"
    elseif (l:tool == 4)
      let l:tool = "cver"
    elseif (l:tool == 5)
      let l:tool = "leda"
    elseif (l:tool == 6)
      let l:tool = "ncverilog"
    endif
  else
    let l:tool = tolower(a:1)
  endif

  " Choose error level
  if (a:0 <= 1)
    if (l:tool == "vcs")
      let l:mode = inputlist([
            \"1. check all",
            \"2. ignore lint",
            \"3. ignore lint and warnings"
            \])
      echo "\n"
    elseif (
      \ l:tool == "msim" ||
      \ l:tool == "cver" ||
      \ l:tool == "ncverilog"
      \ )
      let l:mode = inputlist([
            \"1. check all",
            \"2. ignore warnings"
            \])
      echo "\n"
    endif
  else
    let l:mode = a:2
  endif

  if (l:tool == "vcs")
    " Error messages
    set errorformat=%E%trror-\[%.%\\+\]\ %m
    set errorformat+=%C%m\"%f\"\\,\ %l%.%#
    set errorformat+=%C%f\\,\ %l
    set errorformat+=%C%\\s%\\+%l:\ %m
    set errorformat+=%C%m\"%f\"\\,%.%#
    set errorformat+=%Z%p^                      "Column pointer
    set errorformat+=%C%m                       "Catch all rule
    set errorformat+=%Z%m                       "Finalization messages
    " Warning messages
    if (l:mode <= 2)
      set errorformat+=%W%tarning-\[%.%\\+]\\$
      set errorformat+=%-W%tarning-[LCA_FEATURES_ENABLED]\ Usage\ warning    "Ignore LCA enabled warning
      set errorformat+=%W%tarning-\[%.%\\+\]\ %m
    endif
    " Lint message
    if (l:mode <= 1)
      set errorformat+=%I%tint-\[%.%\\+\]\ %m
    endif
    echo "Selected VCS errorformat"
    "TODO Add support for:
    "Error-[SE] Syntax error
    "  Following verilog source has syntax error :
    "  "../../rtl_v/anadigintf/anasoftramp.v", 128: token is 'else'
    "          else
  endif
  if (l:tool == "msim")
    " Error messages
    set errorformat=\*\*\ Error:\ %f(%l):\ %m
    " Warning messages
    if (l:mode <= 1)
      set errorformat+=\*\*\ Warning:\ \[\%n\]\ %f(%l):\ %m
    endif
    echo "Selected Modelsim errorformat"
  endif
  if (l:tool == "iverilog")
    set errorformat=%f:%l:\ %m
    echo "Selected iverilog errorformat"
  endif
  if (l:tool == "cver")
    " Error messages
    set errorformat=\*\*%f(%l)\ ERROR\*\*\ \[%n\]\ %m
    " Warning messages
    if (l:mode <= 1)
      set errorformat+=\*\*%f(%l)\ WARN\*\*\ \[%n\]\ %m,\*\*\ WARN\*\*\ \[\%n\]\ %m
    endif
    echo "Selected cver errorformat"
  endif
  if (l:tool == "leda")
    " Simple errorformat:
    set errorformat=%f:%l:\ %.%#\[%t%.%#\]\ %m
    "TODO Review -> Multiple line errorformat:
    "set errorformat=%A\ %#%l:%.%#,%C\ \ \ \ \ \ \ \ %p^^%#,%Z%f:%l:\ %.%#[%t%.%#]\ %m
    echo "Selected Leda errorformat"
  endif
  if (l:tool == "ncverilog")
    " Based on https://github.com/vhda/verilog_systemverilog.vim/issues/88
    set errorformat=%.%#:\ \*%t\\,%.%#\ \(%f\\,%l\|%c\):%m
    set errorformat+=%.%#\ *%t\\,%.%#(%f\\,%l\|%c):\ %m
    " Assertion notices don't have column information
    set errorformat+=%.%#\ *%t\\,%.%#(%f\\,%l):\ %m
    " Add ability to parse NULL pointer errors:
    set errorformat+=%E%>%.%#\ *E\\,%m,%C%.%#File:\ %f\\,\ line\ =\ %l\\,\ pos\ =\ %c,%Z%m
    if (l:mode > 1)
      " Ignore warnings
      set errorformat^=%-G%.%#\ \*W\\,%.%#(%f\\,%l\|%c):\ %m
    endif
    echo "Selected NCVerilog errorformat"
  endif
  " Append UVM errorformat if enabled
  if (exists("g:verilog_efm_uvm"))
    set errorformat+=UVM_%tRROR\ %f(%l)\ %m
    set errorformat+=UVM_%tATAL\ %f(%l)\ %m
  endif
endfunction
" }}} 

" vi: sw=2 sts=2 fdm=marker:
