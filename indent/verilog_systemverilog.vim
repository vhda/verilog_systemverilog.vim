" Language: Verilog/SystemVerilog HDL
"
" Credits:
"   Originally created by
"       Lewis Russell <lewis6991@gmail.com>
"
"   Inspired from script originally created by
"       Chih-Tsun Huang <cthuang@larc.ee.nthu.edu.tw>
"
" Buffer Variables:
"     b:verilog_indent_modules : Indentation within module blocks.
"     b:verilog_indent_width   : Indenting width.
"     b:verilog_indent_verbose : Print debug info for each indent.

" Only load this indent file when no other was loaded.
if exists("b:did_indent")
  finish
endif
let b:did_indent = 1

setlocal indentexpr=GetVerilogSystemVerilogIndent()
setlocal indentkeys=!^F,o,O,0),0},=begin,=end,=join,=endcase,=join_any,=join_none
setlocal indentkeys+==endmodule,=endfunction,=endtask,=endspecify
setlocal indentkeys+==endclass,=endpackage,=endsequence,=endclocking
setlocal indentkeys+==endinterface,=endgroup,=endprogram,=endproperty
setlocal indentkeys+==`else,=`endif
setlocal indentkeys+==else

let s:vlog_open_statement    = '\(\<or\>\|[<>:!=?&|^%/*+-]\)'
let s:vlog_comment           = '\(//.*\|/\*.*\*/\)'
let s:vlog_macro             = '`\k\+\((.*)\)\?\s*$'
let s:vlog_statement         = '.*;\s*$\|'. s:vlog_macro
let s:vlog_sens_list         = '\(@\s*(.*)\)'
let s:vlog_always            = '\<always\(_ff\|_comb\|_latch\)\?\>\s*' . s:vlog_sens_list . '\?'
let s:vlog_block_delcaration = '\(\(\<while\>\|\<if\>\|\<foreach\>\|\<for\>\)\s*(\)\|\<else\>\|\<do\>\|' . s:vlog_always
let s:vlog_method            = '^\(\s*pure\s\+virtual\|\s*extern\)\@!.*\(function\|task\)\s\+\w\+'

let s:vlog_block_start       = '\<\(begin\|case\|fork\)\>\|{\|('
let s:vlog_block_end         = '\(\<\(end\|endcase\|join\(_all\|_none\)\?\)\>\|}\|)\)'
let g:vlog_block_start       = 'begin\|case\|fork'
let g:vlog_block_end         = '\(end\|endcase\|join\(_all\|_none\)\?\)'

let s:vlog_module            = '\<\(extern\s\+\)\@!module\>'
let s:vlog_property          = '\(\(assert\|assume\|cover\)\s\+\)\@<!property'
let s:vlog_case              = '\<case[zx]\?\>\s*(.*)'
let s:vlog_join              = '\<join\(_all\|_none\)\?\>'

let s:vlog_context_start     = '^\s*`ifn\?def\|\<\(class\|program\|sequence\|interface\|' . s:vlog_module . '\|' . s:vlog_property . '\)\>\|' . s:vlog_method
let s:vlog_context_end       = '\<end\(function\|class\|' . s:vlog_module . '\|programm\|property\|sequence\|interface\|task\)\>\|^\s*`endif'

" Only define the function once.
if exists("*GetVerilog_SystemVerilogIndent")
  finish
endif

set cpo-=C

function! GetVerilogSystemVerilogIndent()

  let s:vverb = exists('b:verilog_indent_verbose')

  if exists('b:verilog_indent_width')
    let s:offset = b:verilog_indent_width
  else
    let s:offset = &sw
  endif

  " At the start of the file use zero indent.
  if v:lnum == 1
    return 0
  endif

  let s:curr_line = getline(v:lnum)

  " Reset indent for end blocks.
  if s:curr_line =~ '^\s*\<endfunction\>'
    return SearchBackForPattern('\<function\>', v:lnum)
  elseif s:curr_line =~ '^\s*\<endtask\>'
    return SearchBackForPattern('\<task\>', v:lnum)
  elseif s:curr_line =~ '^\s*\<endclocking\>'
    return SearchBackForPattern('\<clocking\>', v:lnum)
  elseif s:curr_line =~ '^\s*\<endpackage\>'
    return SearchBackForPattern('\<package\>', v:lnum)
  elseif s:curr_line =~ '^\s*\<endmodule\>'
    return SearchBackForPattern('\<module\>', v:lnum)
  elseif s:curr_line =~ '^\s*\<endinterface\>'
    return SearchBackForPattern('\<interface\>', v:lnum)
  elseif s:curr_line =~ '^\s*\<endproperty\>'
    return SearchBackForPattern('\<property\>', v:lnum)
  elseif s:curr_line =~ '^\s*\<endgroup\>'
    return SearchBackForPattern('\<covergroup\>', v:lnum)
  elseif s:curr_line =~ '^\s*\<endspecify\>'
    return SearchBackForPattern('\<specify\>', v:lnum)
  elseif s:curr_line =~ '^\s*\<endsequence\>'
    return SearchBackForPattern('\<sequence\>', v:lnum)
  elseif s:curr_line =~ '^\s*)'
    return indent(SearchBackForNestableContextStart('(', '', ')', v:lnum))
  elseif s:curr_line =~ '^\s*\<while\>\s*(.*);'
    return indent(SearchBackForNestableContextStart('\<do\>', '', '\<while\>\s*(.*);', v:lnum))
  elseif s:curr_line =~ '^\s*}'
    return indent(SearchBackForNestableContextStart('{', '', '}', v:lnum))
  elseif s:curr_line =~ '^\s*\<endclass\>'
    return indent(SearchBackForNestableContextStart('\<class\>', '', '\<endclass\>', v:lnum))
  elseif s:curr_line =~ '^\s*\<end\>'
    return indent(SearchBackForNestableContextStart('\<begin\>', '', '\<end\>', v:lnum))
  elseif s:curr_line =~ '^\s*`\(endif\|else\|elsif\)'
    return indent(SearchBackForNestableContextStart('`ifn\?def', '`else\|`elsif', '`endif', v:lnum))
  elseif s:curr_line =~ '^\s*\<join\(_all\|_none\)\?\>'
    return indent(SearchBackForNestableContextStart('\<fork\>', '', s:vlog_join, v:lnum))
  elseif s:curr_line =~ '^\s*\<endcase\>'
    return indent(SearchBackForNestableContextStart(s:vlog_case, '', '\<endcase\>', v:lnum))
  else
    return GetContextIndent(v:lnum)
  endif

endfunction

function! StripComments(lnum)
  let l:temp = getline(a:lnum)

  " Remove inline comments
  if l:temp !~ '^\s*'.s:vlog_comment.'\s*$'
    let l:temp = substitute(l:temp, '/\*.\{-}\*/\|//.*', '', 'g')
  endif

  return l:temp
endfunction

function! SearchBackForPattern(pattern, current_line_no)
  let l:lnum = a:current_line_no

  while l:lnum > 0
    let l:lnum = search(a:pattern, 'bW')
    if getline(l:lnum) !~ s:vlog_comment
      call Debug("Reset indent for context end -> " . a:keyword)
      return indent(l:lnum)
    endif
  endwhile

endfunction

" For any kind of block with a provided end pattern and start pattern, return the
" line of the start of the block.
function! SearchBackForNestableContextStart(start_wd, mid_wd, end_wd, current_line_no)
  call cursor(a:current_line_no, 1)

  if a:mid_wd == ''
    let l:skip_arg = "getline('.') =~ '/[/*]\\s*\\(" . a:start_wd . '\|' . a:end_wd . "\\)'"
  else
    let l:skip_arg = "getline('.') =~ '/[/*]\\s*\\(" . a:start_wd . '\|' . a:end_wd . '\|' . a:mid_wd . "\\)'"
  endif

  " This works but is alot slower than the above. Use this if there are problems.
  " let l:skip_arg = 'synIDattr(synID(".", col("."), 0), "name") == "verilogComment"'

  return searchpair(a:start_wd, a:mid_wd, a:end_wd, 'bnW', l:skip_arg)
endfunction

function! IsBlockEnd(line)
  let s:curr_line_level =
        \   CountMatches(a:line, s:vlog_block_end  )
        \ - CountMatches(a:line, s:vlog_block_start)

  if s:curr_line_level == 1 &&
        \ a:line !~ s:vlog_comment &&
        \ a:line =~ '^\s*' . s:vlog_block_end
    return 1
  endif
endfunction

function! GetContextIndent(current_line_no)
  let l:block_level    = 0
  let l:bracket_level  = 0
  let l:cbracket_level = 0
  let l:fork_level     = 0
  let l:case_level     = 0

  let l:lnum = a:current_line_no
  let l:oneline_mode = 1
  let l:look_for_open_statement = 1

  if IsBlockEnd(s:curr_line)
    let l:offset = 0
  else
    let l:offset = s:offset
  endif

  " Loop that searches up the file to build a context and determine the correct
  " indentation.
  while l:lnum > 1

    let l:lnum = prevnonblank(l:lnum - 1)
    let l:line = getline(l:lnum)

    " Never use comments to determine indentation.
    if l:line =~ '^\s*' . s:vlog_comment
      continue
    endif

    let l:line = StripComments(l:lnum)

    call Debug("GetContextIndent:" . l:lnum . ": " . l:line)

    if l:look_for_open_statement == 1
      if l:line =~ s:vlog_open_statement . '\s*$' ||
            \ (s:curr_line =~ '^\s*' . s:vlog_open_statement &&
            \ s:curr_line !~ s:vlog_comment)
        let l:offset += s:offset
        call Debug("Increasing indent for an open statment.")
      endif
      let l:look_for_open_statement = 0
    endif

    " If we hit an 'end', 'endcase' or 'join', skip past the whole block.
    if l:line =~ '\<end\>'
      let l:lnum = SearchBackForNestableContextStart('\<begin\>', '', '\<end\>', l:lnum)
      let l:oneline_mode = 0
      let l:block_level = 1
      let l:line = StripComments(l:lnum)
    endif

    if l:line =~ s:vlog_join
      let l:lnum = SearchBackForNestableContextStart('\<fork\>', '', s:vlog_join, l:lnum)
      let l:oneline_mode = 0
      let l:fork_level = 1
      let l:line = StripComments(l:lnum)
    endif

    if l:line =~ '\<endcase\>'
      let l:lnum = SearchBackForNestableContextStart(s:vlog_case, '', '\<endcase\>', l:lnum)
      let l:oneline_mode = 0
      let l:case_level = 1
      let l:line = StripComments(l:lnum)
    endif

    let l:block_level -= l:line =~ '\<begin\>'
    let l:fork_level  -= l:line =~ '\<fork\>'
    let l:case_level  -= l:line =~ s:vlog_case

    if l:line =~ '[()]'
      let l:bracket_level  += CountMatches(l:line, ')') - CountMatches(l:line, '(')
    endif

    if l:line =~ '[{}]'
      let l:cbracket_level += CountMatches(l:line, '}') - CountMatches(l:line, '{')
    endif

    if l:block_level < 0
      call Debug("Inside a 'begin end' block.")
      return indent(l:lnum) + l:offset
    elseif l:bracket_level < 0
      call Debug("Inside a '()' block.")
      return indent(l:lnum) + l:offset
    elseif l:cbracket_level < 0
      call Debug("Inside a '{}' block.")
      return indent(l:lnum) + l:offset
    elseif l:fork_level < 0
      call Debug("Inside a 'fork join' block.")
      return indent(l:lnum) + l:offset
    elseif l:case_level < 0
      call Debug("Inside a 'case endcase' block.")
      return indent(l:lnum) + l:offset
    endif

    if l:oneline_mode == 1 && l:line =~ s:vlog_statement
      let l:oneline_mode = 0
    elseif l:oneline_mode == 1 && l:line =~ s:vlog_block_delcaration
      if s:curr_line =~ '^\s*\<begin\>' && l:block_level == 0
        call Debug("Standalone 'begin' after block declaration.")
        return indent(l:lnum)
      elseif s:curr_line =~ '^\s*{' && l:cbracket_level == 0
        call Debug("Standalone '{' after block declaration.")
        return indent(l:lnum)
      elseif s:curr_line =~ '^\s*(' && l:bracket_level == 0
        call Debug("Standalone '(' after block declaration.")
        return indent(l:lnum)
      else
        call Debug("Indenting a single line block.")
        return indent(l:lnum) + l:offset
      endif
    elseif s:curr_line =~ '^\s*else' &&
          \ l:line =~ '\<\(if\|assert\)\>\s*(.*)' &&
          \ l:block_level == 0
      call Debug("'else' of 'if' or 'assert'.")
      return indent(l:lnum)
    endif

    if l:line =~ s:vlog_context_start
      if l:line =~ s:vlog_module
        call Debug("Inside a module.")
        if exists('b:verilog_indent_modules')
          return indent(l:lnum) + s:offset
        else
          return indent(l:lnum)
        endif
      else
        call Debug("Inside a context.")
        return indent(l:lnum) + l:offset
      endif
    elseif l:line =~ s:vlog_context_end
      call Debug("After the end of a context.")
      return indent(l:lnum)
    endif

  endwhile
endfunction

function! CountMatches(line, pattern)
  return len(split(a:line, a:pattern, 1)) - 1
endfunction

function! Debug(msg)
  if s:vverb
    echom a:msg
  endif
endfunction

" vi: sw=2 sts=2:
