" Verilog/SystemVerilog support functions
" Language:     Verilog/SystemVerilog
" Maintainer:   Vitor Antunes <vitor.hda@gmail.com>

"------------------------------------------------------------------------
" Omni completion functions
" {{{
"
" Requires ctags from:
" https://github.com/fishman/ctags
" https://github.com/exuberant-ctags/ctags
" ctags must be run with --extra=+q
function! verilog_systemverilog#Complete(findstart, base)
" {{{
  "------------------------------------------------------------------------
  " Phase 1: Find and return prefix of completion
  " s:word   contains the keyword to be completed
  " s:prefix contains the "name." prefix preceding s:word
  " s:instname name of the instance ("." completion only)
  " s:module name of the instance ("." completion only)
  if a:findstart
    let linenr = line('.')
    let line = getline('.')
    let start = col('.')
    let prefixpos = -1
    let s:instname = ''
    let s:module = ''

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

      " If the prefix is simply a "." assume that this is an instance
      " port connection and search for its declaration
      if s:prefix == '.'
        " Get instance info and break from while loop
        let values = s:GetInstanceInfo(linenr, start)
        let s:instname = values[0]
        let s:module = values[1]
      endif
    endif

    return prefixpos
  endif

  "------------------------------------------------------------------------
  " Phase 2: Search for type definition in tags file
  if exists("s:prefix") && s:prefix != ''
    call verilog_systemverilog#Verbose("Prefix: " . s:prefix)
    call verilog_systemverilog#Verbose("Word  : " . s:word)
    if s:module != ''
      " Process an instance
      call verilog_systemverilog#Verbose("Process instance")
      if exists("s:word")
        let tags = taglist('^' . s:module . '\.' . s:word)
      else
        let tags = taglist('^' . s:module . '\.')
      endif
      call verilog_systemverilog#Verbose("Number of tags found: " . len(tags))
      if s:instname != ''
        " In instances only return ports
        let tags = s:TagsFilterPorts(tags)
        " Filter out hierarchical ports
        call filter(tags, 'len(split(v:val["name"], "\\.")) > 2 ? 0 : 1')
        call verilog_systemverilog#Verbose("Number of tags after filtering: " . len(tags))
        " Remove the module name prefix
        call map(tags, 'strpart(v:val["name"], len(s:module . "."))')
        if (v:version >= 704)
          return {'words' : tags}
        else
          return tags
        endif
      else
        " In parameter list only return constants
        let tags = s:TagsFilterConstants(tags)
        " Filter out hierarchical ports
        call filter(tags, 'len(split(v:val["name"], "\\.")) > 2 ? 0 : 1')
        call verilog_systemverilog#Verbose("Number of tags after filtering: " . len(tags))
        " Remove the module name prefix
        call map(tags, 'strpart(v:val["name"], len(s:module . "."))')
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
      let tags = s:TagsFilterPortsOrConstants(taglist('^' . base . '\.'))
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
" }}}

" Search file for instance information:
" * name
" * type (typically a module name, but can also be a function/task/etc)
" * line number
function! s:GetInstanceInfo(linenr, column)
" {{{
  let linenr = a:linenr
  let line = getline(linenr)
  let start = a:column
  let instname = ""
  let module = ""
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
          let module = strpart(line, 0, ininsttype)
        else
          let module = strpart(line, start, ininsttype - start)
        endif
        call verilog_systemverilog#Verbose("Found instance type \"" . module . "\", on line " . linenr)
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

  call verilog_systemverilog#Verbose("Found instance. Name: »" . instname . "« Type: »" . module . "«")
  return [instname, module, linenr]
endfunction
" }}}

" Append signature to functions and tasks
function s:AppendSignature(tags)
" {{{
  let newtags = []
  for t in a:tags
    if t["kind"] == "t" || t["kind"] == "f"
      let t["name"] = t["name"] . "()"
    endif
    call add(newtags, t)
  endfor
  return newtags
endfunction
" }}}

" Get list of inheritance tags
function s:GetInheritanceTags(class, object)
" {{{
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
" }}}

" Searches for declaration of "word" and returns its type
function s:GetVariableType(word)
" {{{
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
" }}}

" Searches for declaration of "object" and returns "parameter" initialization value
function s:GetObjectParameterValue(object, parameter)
" {{{
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
" }}}

" Searches for declaration of "class" and returns default "parameter" value
function s:GetClassDefaultParameterValue(class, parameter)
" {{{
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
" }}}

" Filter tag list to only return ports
function s:TagsFilterPorts(tags)
" {{{
  let tags = a:tags
  call filter(tags, 'has_key(v:val, "kind") ? v:val["kind"] == "p" : 1')
  return tags
endfunction
" }}}

" Filter tag list to only return constants
function s:TagsFilterConstants(tags)
" {{{
  let tags = a:tags
  call filter(tags, 'has_key(v:val, "kind") ? v:val["kind"] == "c" : 1')
  return tags
endfunction
" }}}

" Filter tag list to only return ports or constants
function s:TagsFilterPortsOrConstants(tags)
" {{{
  let tags = a:tags
  call filter(tags, 'has_key(v:val, "kind") ? v:val["kind"] == "p" || v:val["kind"] == "c" : 1')
  return tags
endfunction
" }}}
" }}}

"------------------------------------------------------------------------
" Common functions
" {{{
" Verbose messaging
" Only displays messages if b:verilog_verbose or g:verilog_verbose is defined
function verilog_systemverilog#Verbose(message)
" {{{
  if verilog_systemverilog#VariableExists("verilog_verbose")
    echom a:message
  endif
endfunction
" }}}

" Configuration control
" Pushes value to list only if new
" Based on: http://vi.stackexchange.com/questions/6619/append-to-global-variable-and-completion
function verilog_systemverilog#PushToVariable(variable, value)
" {{{
  let list = verilog_systemverilog#VariableGetValue(a:variable)
  if (count(list, a:value) == 0)
    call add(list, a:value)
  endif
  call verilog_systemverilog#VariableSetValue(a:variable, list)
endfunction
" }}}

function verilog_systemverilog#PopFromVariable(variable, value)
" {{{
  let list = verilog_systemverilog#VariableGetValue(a:variable)
  call verilog_systemverilog#VariableSetValue(a:variable, filter(list, "v:val !=# a:value"))
endfunction
" }}}

" Get variable value
" Searches for both b:variable and g:variable, with this priority.
" If the variable name includes '_lst' it is automatically split into a
" list.
function verilog_systemverilog#VariableGetValue(variable)
" {{{
  if exists('b:' . a:variable)
    let value = eval('b:' . a:variable)
  elseif exists('g:' . a:variable)
    let value = eval('g:' . a:variable)
  else
    let value = ''
  endif
  if a:variable =~ '_lst'
    return split(value, ',')
  else
    return value
  endif
endfunction
" }}}

" Set variable value
" Searches for both b:variable and g:variable, with this priority.
" If none exists, g: will be used
" If the variable name includes '_lst' the value argument is assumed to
" be a list.
function verilog_systemverilog#VariableSetValue(variable, value)
" {{{
  if a:variable =~ '_lst'
    let value = join(a:value, ',')
  else
    let value = a:value
  endif
  if exists('b:' . a:variable)
    exec 'let b:' . a:variable . ' = value'
  else
    exec 'let g:' . a:variable . ' = value'
  endif
endfunction
" }}}

" Checks for variable existence
function verilog_systemverilog#VariableExists(variable)
" {{{
  return exists('b:' . a:variable) || exists('g:' . a:variable)
endfunction
" }}}
" }}}

"------------------------------------------------------------------------
" Command completion functions
" {{{
function verilog_systemverilog#CompleteCommand(lead, command, cursor)
" {{{
  " Get list with current values in variable
  if (a:command =~ 'Folding')
    let current_values = verilog_systemverilog#VariableGetValue("verilog_syntax_fold_lst")
  elseif (a:command =~ 'Indent')
    let current_values = verilog_systemverilog#VariableGetValue("verilog_disable_indent_lst")
  elseif (a:command =~ 'ErrorUVM')
    let current_values = verilog_systemverilog#VariableGetValue("verilog_efm_uvm_lst")
  endif

  " Create list with valid completion values depending on command type
  if (a:command =~ 'FoldingAdd')
    let valid_completions = [
          \ 'all',
          \ 'class',
          \ 'function',
          \ 'task',
          \ 'specify',
          \ 'interface',
          \ 'clocking',
          \ 'covergroup',
          \ 'sequence',
          \ 'property',
          \ 'comment',
          \ 'define',
          \ 'instance'
          \ ]
    if (exists('g:verilog_syntax_custom'))
      let valid_completions += keys(g:verilog_syntax_custom)
    endif
    if (empty(filter(current_values, 'v:val =~ "^block"')))
      let valid_completions += [
            \ 'block',
            \ 'block_nested',
            \ 'block_named'
            \ ]
    endif
    for item in current_values
      call filter(valid_completions, 'v:val !=# item')
    endfor
  elseif (a:command =~ 'DisableIndentAdd')
    let valid_completions = [
          \ 'module',
          \ 'interface',
          \ 'class',
          \ 'package',
          \ 'covergroup',
          \ 'program',
          \ 'generate',
          \ 'sequence',
          \ 'property',
          \ 'method',
          \ 'preproc',
          \ 'conditional',
          \ 'eos',
          \ 'standalone'
          \ ]
    for item in current_values
      call filter(valid_completions, 'v:val !=# item')
    endfor
  elseif (a:command =~ 'ErrorUVMAdd')
    let valid_completions = [
          \ 'all',
          \ 'info',
          \ 'warning',
          \ 'error',
          \ 'fatal',
          \ ]
    for item in current_values
      call filter(valid_completions, 'v:val !=# item')
    endfor
  else
    let valid_completions = current_values
  endif

  " If a:lead already includes other comma separated values, then remove
  " all from the list of valid values except the last
  let lead_list = split(a:lead, ',')
  call verilog_systemverilog#Verbose('Current lead values list: [' . join(lead_list, ',') . '] (length = ' . len(lead_list) . ')')
  call verilog_systemverilog#Verbose('Valid completions: [' . join(valid_completions, ',') . '] (length = ' . len(valid_completions) . ')')
  if (a:lead =~ ',$')
    let initial_lead = lead_list
    let real_lead = ""
  else
    if (len(lead_list) > 1)
      let initial_lead = lead_list[0:-2]
      let real_lead = lead_list[-1]
    else
      let initial_lead = []
      let real_lead = a:lead
    endif
  endif
  call verilog_systemverilog#Verbose('Removing [' . join(initial_lead, ',') . '] from completion value list')
  call verilog_systemverilog#Verbose('Searching using lead: "' . real_lead . '"')
  for item in initial_lead
    call filter(valid_completions, 'v:val !=# item')
  endfor

  let completion_list = filter(valid_completions, 'v:val =~ "^" . real_lead')

  if (len(initial_lead) > 0)
    return map(completion_list, 'join(initial_lead, ",") . "," . v:val')
  else
    return completion_list
  endif
endfunction
" }}}
" }}}

"------------------------------------------------------------------------
" External functions
" {{{
function verilog_systemverilog#GotoInstanceStart(line, column)
" {{{
  let values = s:GetInstanceInfo(a:line, col('$'))
  if values[2] != ""
    call cursor(values[2], a:column)
  endif
endfunction
" }}}

function verilog_systemverilog#FollowInstanceTag(line, column)
" {{{
  let values = s:GetInstanceInfo(a:line, col('$'))
  if exists("g:verilog_navigate_split")
    exec "wincmd ".g:verilog_navigate_split
  endif
  if values[1] != ""
    execute "tag " . values[1]
  endif
endfunction
" }}}

function verilog_systemverilog#ReturnFromInstanceTag()
" {{{
  if winnr('$') > 1 && exists("g:verilog_navigate_split")
    if exists("g:verilog_navigate_split_close")
      exec g:verilog_navigate_split_close
    else
      exec "quit"
    endif
  else
    exec "pop"
  endif
endfunction
" }}}

function verilog_systemverilog#FollowInstanceSearchWord(line, column)
" {{{
  let @/='\<'.expand("<cword>").'\>'
  call verilog_systemverilog#FollowInstanceTag(a:line, a:column)
  exec "normal!" . @/
  normal! n
endfunction
" }}}
" }}}

"------------------------------------------------------------------------
" Command to control errorformat and compiler
" {{{
function! verilog_systemverilog#VerilogErrorFormat(...)
" {{{
  " Choose tool
  if (a:0 == 0)
    let l:tool = inputlist([
          \"1. VCS",
          \"2. Modelsim",
          \"3. iverilog",
          \"4. cver",
          \"5. Leda",
          \"6. Verilator",
          \"7. NCVerilog",
          \"8. SpyGlass",
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
      let l:tool = "verilator"
    elseif (l:tool == 7)
      let l:tool = "ncverilog"
    else
      let l:tool = "spyglass"
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
      \ l:tool == "verilator" ||
      \ l:tool == "ncverilog" ||
      \ l:tool == "spyglass"
      \ )
      let l:mode = inputlist([
            \"1. check all",
            \"2. ignore warnings"
            \])
      echo "\n"
      if (l:mode == 2)
        let l:mode = 3
      endif
    else
      let l:mode = 1
    endif
  else
    let l:mode = a:2
  endif

  if (l:mode <= 1)
    let g:verilog_efm_level = "lint"
  elseif (l:mode <= 2)
    let g:verilog_efm_level = "warning"
  else
    let g:verilog_efm_level = "error"
  endif

  call verilog_systemverilog#Verbose("Configuring errorformat with: tool=" . l:tool . "; mode=" . l:mode)

  if (index(['vcs', 'modelsim', 'iverilog', 'cver', 'leda', 'verilator', 'ncverilog', 'spyglass'], l:tool) >= 0)
    execute 'compiler! '. l:tool
    echo 'Selected errorformat for "' . l:tool . '"'
  else
    echoerr 'Unknown tool name "' . l:tool . '"'
  endif
endfunction
" }}}
" }}}

" vi: sw=2 sts=2 fdm=marker:
