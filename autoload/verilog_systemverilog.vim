" Vim completion script
" Language:     Verilog/SystemVerilog
" Maintainer:   Vitor Antunes <vitor.hda@gmail.com>

" Requires ctags from:
" https://github.com/fishman/ctags
" https://github.com/exuberant-ctags/ctags
" ctags must be run with --extra=+q
function! verilog_systemverilog#Complete(findstart, base)
  if a:findstart
    let linenr = line('.')
    let line = getline('.')
    let start = col('.')
    let wordpos = start
    let prefixpos = -1
    let s:instname = ''
    let s:insttype = ''

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
        elseif line[start - 1] =~ '\(\s\|(\)'
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

  " Search for type definition in tags file
  if exists("s:prefix") && s:prefix != ''
    call s:Verbose("Prefix: " . s:prefix)
    call s:Verbose("Word  : " . s:word)
    if s:instname != ''
      " Process an instance
      if s:insttype != ''
        if exists("s:word")
          let tags = taglist('^' . s:insttype . "." . s:word)
        else
          let tags = taglist('^' . s:insttype)
        endif
        call s:Verbose("Number of tags found: " . len(tags))
        " In instances only return ports
        let tags = s:FilterPorts(tags)
        " Filter out hierarchical ports
        call filter(tags, 'len(split(v:val["name"], "\\.")) > 2 ? 0 : 1')
        call s:Verbose("Number of tags after filtering: " . len(tags))
        " Remove the module name prefix
        call map(tags, 'strpart(v:val["name"], len(s:insttype . "."))')
        return {'words' : tags}
      " Check if it is a function/task call
      else
        call s:Verbose("Searching for function")
        let items = split(s:instname, '\.')
        if len(items) > 1
          let word_list = [s:GetVariableType(items[0])]
          call extend(word_list, items[1:])
          let base = join(word_list, ".")
        elseif len(items) == 1
          let base = s:instname
        endif
        let tags = s:FilterPorts(taglist('^' . base))
        call map(tags, 'strpart(v:val["name"], len(base . "."))')
        return {'words' : tags}
      endif
    else
      " Process an object
      let idx = match(s:prefix, '\.')
      if idx >= 0
        let word = strpart(s:prefix, 0, idx)
      else
        let word = s:prefix
      endif

      let type = s:GetVariableType(word)
      if type != ""
        let tags = taglist('^' . type)
        if len(tags) == 0
          return -1
        endif
        " Append () to functions and tasks
        let newtags = []
        for t in tags
          if t["kind"] == "t" || t["kind"] == "f"
            let t["name"] = t["name"] . "()"
          endif
          call add(newtags, t)
        endfor
        let tags = newtags
        " Filter out hierarchical ports
        call filter(tags, 'len(split(v:val["name"], "\\.")) > 2 ? 0 : 1')
        " Remove the variable type prefix
        call map(tags, 'strpart(v:val["name"], len(s:prefix)+1)')
        return {'words' : tags}
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
function! s:GetInstanceInfo(linenr, column)
  let linenr = a:linenr
  let line = getline(linenr)
  let start = a:column
  let instname = ""
  let insttype = ""
  let ininstdecl = 0
  let ininsttype = 0
  let p = 0

  call s:Verbose("Searching for instance info, starting on line " . linenr)
  while linenr > 0
    while start > 0
      " Give up if a ; is found.
      if line[start - 1] == ';'
        call s:Verbose("Giving up instance info search, on line " . linenr)
        break
      " Skip over (...)
      elseif line[start - 1] == ')' || p > 0
        if line[start - 1] == ')'
          call s:Verbose("Skipping parentheses, started on line " . linenr)
          let p += 1
        endif
        while start > 0
          if line[start - 1] == '('
            let p -= 1
            call s:Verbose("Skipping parentheses, ended on line " . linenr)
            break
          endif
          let start -= 1
        endwhile
      " An unmatched opening parentheses indicate start of instance
      " From here backward search for the instance declaration
      elseif line[start - 1] == '(' && p == 0
        let ininstdecl = -1
        call s:Verbose("Found instance declaration name start, on line " . linenr)
      elseif ininstdecl < 0 && line[start - 1] =~ '\w'
        let ininstdecl = start
      elseif ininstdecl > 0 && ininsttype == 0 && (line[start - 1] =~ '\s' || start == 1)
        if start == 1 && line[start - 1] !~ '\s'
          let instname = strpart(line, 0, ininstdecl)
        else
          let instname = strpart(line, start, ininstdecl - start)
        endif
        call s:Verbose("Found instance name \"" . instname . "\", on line " . linenr)
        let ininsttype = -1
      elseif ininsttype < 0 && line[start - 1] =~ '\w'
        let ininsttype = start
      elseif ininsttype > 0 && (line[start - 1] =~ '\s' || start == 1)
        if start == 1 && line[start - 1] !~ '\s'
          let insttype = strpart(line, 0, ininsttype)
        else
          let insttype = strpart(line, start, ininsttype - start)
        endif
        call s:Verbose("Found instance type \"" . insttype . "\", on line " . linenr)
        break
      endif

      let start -= 1
    endwhile

    " Break search when both instance name and type were found
    if ininsttype > 0 && ininstdecl > 0
      break
    endif

    " Give up if a ; is found.
    if line[start - 1] == ';'
      call s:Verbose("Giving up instance info search, on line " . linenr)
      break
    endif

    " Check next line
    let linenr -= 1
    let line = getline(linenr)
    let start = len(line)
  endwhile

  call s:Verbose("Found instance. Name: »" . instname . "« Type: »" . insttype . "«")
  return [instname, insttype]
endfunction

" Searches for declaration of "word" and returns its type
function s:GetVariableType(word)
  if searchdecl(a:word, 0) == 0
    let line = getline('.')
    let type = split(line)[0]
    call s:Verbose("Found declation for: " . a:word . " (" . type . ")")
    return type
  endif
  return 0
endfunction

" Filter tag list to only return ports
function s:FilterPorts(tags)
  let tags = a:tags
  call filter(tags, 'has_key(v:val, "kind") ? v:val["kind"] == "p" : 1')
  return tags
endfunction

" Verbose messaging
" Only displays messages if b:verilog_omni_verbose is defined
function s:Verbose(message)
  if exists("b:verilog_omni_verbose")
    echom a:message
  endif
endfunction

" vi: sw=2 st=2:
