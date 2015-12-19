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
let s:vlog_macro             = '`\k\+\((.*)\)\?$'
let s:vlog_statement         = '.*;$\|'. s:vlog_macro
let s:vlog_sens_list         = '\(@\s*(.*)\)'
let s:vlog_always            = '\<always\(_ff\|_comb\|_latch\)\?\>\s*' . s:vlog_sens_list . '\?'
let s:vlog_block_delcaration = '\(\(\<while\>\|\<if\>\|\<foreach\>\|\<for\>\)\s*(.*)\)\|\<else\>\|\<do\>\|' . s:vlog_always
let s:vlog_method            = '^\(pure\s\+virtual\|extern\)\@!.*\(function\|task\)\s\+\w\+'

let s:vlog_block_start       = '\<\(begin\|case\|fork\)\>\|{\|('
let s:vlog_block_end         = '\(\<\(end\|endcase\|join\(_all\|_none\)\?\)\>\|}\|)\)'

let s:vlog_module            = '\<\(extern\s\+\)\@!module\>'
let s:vlog_property          = '\(\(assert\|assume\|cover\)\s\+\)\@<!property'

let s:vlog_context_start     = '^`ifn\?def\|\<\(class\|program\|sequence\|interface\|' . s:vlog_module . '\|' . s:vlog_property . '\)\>\|' . s:vlog_method

let s:vlog_context_end       = '\<end\(function\|class\|' . s:vlog_module . '\|programm\|property\|sequence\|interface\|task\)\>\|^`endif'

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

  if exists('b:verilog_indent_modules')
    let s:indent_modules = s:offset
  else
    let s:indent_modules = 0
  endif

  " At the start of the file use zero indent.
  if v:lnum == 1
    return 0
  endif

  let l:curr_line  = StripCommentsAndWS(getline(v:lnum))

  " Reset indent for end blocks.
  if l:curr_line =~ '^\<endfunction\>'
    return SearchBackForPattern('\<function\>', v:lnum)
  elseif l:curr_line =~ '^\<endtask\>'
    return SearchBackForPattern('\<task\>', v:lnum)
  elseif l:curr_line =~ '^\<endclocking\>'
    return SearchBackForPattern('\<clocking\>', v:lnum)
  elseif l:curr_line =~ '^\<endpackage\>'
    return SearchBackForPattern('\<package\>', v:lnum)
  elseif l:curr_line =~ '^\<endmodule\>'
    return SearchBackForPattern('\<module\>', v:lnum)
  elseif l:curr_line =~ '^\<endinterface\>'
    return SearchBackForPattern('\<interface\>', v:lnum)
  elseif l:curr_line =~ '^\<endproperty\>'
    return SearchBackForPattern('\<property\>', v:lnum)
  elseif l:curr_line =~ '^\<endgroup\>'
    return SearchBackForPattern('\<covergroup\>', v:lnum)
  elseif l:curr_line =~ '^\<endspecify\>'
    return SearchBackForPattern('\<specify\>', v:lnum)
  elseif l:curr_line =~ '^\<endsequence\>'
    return SearchBackForPattern('\<sequence\>', v:lnum)
  elseif l:curr_line =~ '^)'
    return SearchBackForNestableContextStart('(', ')', v:lnum)
  elseif l:curr_line =~ '^\<while\>\s*(.*);'
    return SearchBackForNestableContextStart('\<do\>', '\<while\>\s*(.*);', v:lnum)
  elseif l:curr_line =~ '^}'
    return SearchBackForNestableContextStart('{', '}', v:lnum)
  elseif l:curr_line =~ '^\<endclass\>'
    return SearchBackForNestableContextStart('\<class\>', '\<endclass\>', v:lnum)
  elseif l:curr_line =~ '^\<end\>'
    return SearchBackForNestableContextStart('\<begin\>', '\<end\>', v:lnum)
  elseif l:curr_line =~ '^`\(endif\|else\|elsif\)'
    return SearchBackForNestableContextStart('^`ifn\?def', '^`endif', v:lnum)
  else
    return GetContextIndent(v:lnum)
  endif

endfunction

function! StripCommentsAndWS(line)
  " Strip whitespace from start and end of lines
  let l:temp = substitute(a:line, '^\s*\(.*\)\s*$', '\1', 'g')

  " Remove inline comments
  if l:temp !~ '^'.s:vlog_comment.'$'
    let l:temp = substitute(l:temp, '/\*.\{-}\*/\|//.*', '', 'g')
  endif

  return l:temp
endfunction

function! SearchBackForPattern(pattern, current_line_no)
  let l:lnum = a:current_line_no

  while l:lnum > 0
    let l:lnum = prevnonblank(l:lnum - 1)
    let l:line = StripCommentsAndWS(getline(l:lnum))
    if l:line !~ s:vlog_comment && l:line =~ a:pattern
      call Debug("Reset indent for context end -> " . a:keyword)
      return indent(l:lnum)
    endif
  endwhile

endfunction

" For any kind of block with a provided end pattern and start pattern, return the
" indent of the start of the block.
function! SearchBackForNestableContextStart(start_wd, end_wd, current_line_no)
  let l:lnum = a:current_line_no
  let l:block_level = 0

  while l:lnum > 0
    let l:lnum = prevnonblank(l:lnum - 1)
    let l:line = StripCommentsAndWS(getline(l:lnum))

    let l:block_level += len(split(l:line, a:end_wd  , 1)) - 1
    let l:block_level -= len(split(l:line, a:start_wd, 1)) - 1

    if l:block_level < 0
      call Debug("Get indent for end of block -> " . l:line)
      return indent(l:lnum)
    endif
  endwhile
endfunction

function! GetContextIndent(current_line_no)
  let l:context_level = 0
  let l:lnum = a:current_line_no
  let l:curr_line = StripCommentsAndWS(getline(a:current_line_no))
  let l:offset = 0
  let l:oneline_mode = 1
  let l:look_for_open_statment = 1

  let l:curr_line_level  = len(split(l:curr_line, s:vlog_block_end,   1)) - 1
  let l:curr_line_level -= len(split(l:curr_line, s:vlog_block_start, 1)) - 1

  if l:curr_line_level == 1 &&
        \ l:curr_line !~ s:vlog_comment &&
        \ l:curr_line =~ '^' . s:vlog_block_end
    let l:offset = 0
  else
    let l:offset = s:offset
  endif

  while l:lnum > 1

    let l:lnum = prevnonblank(l:lnum - 1)
    let l:line = StripCommentsAndWS(getline(l:lnum))

    call Debug("GetContextIndent:" . l:lnum . ": " . l:line)

    if l:line =~ s:vlog_comment
      continue
    endif

    if l:look_for_open_statment == 1
      if l:line =~ s:vlog_open_statement . '$'
        call Debug("Increasing indent for an open statment.")
        let l:offset += s:offset
      endif
    endif

    let l:look_for_open_statment = 0

    let l:context_level += len(split(l:line, s:vlog_block_end  , 1)) - 1
    let l:context_level -= len(split(l:line, s:vlog_block_start, 1)) - 1

    if l:line =~ s:vlog_statement ||
          \ l:line =~ '\<end\(case\)\?\>'
      let l:oneline_mode = 0
    elseif l:oneline_mode == 1 &&
          \ l:line =~ s:vlog_block_delcaration
      if l:curr_line =~ '^\<begin\>\|^{\|^(' &&
            \ l:context_level == 0
        call Debug("Standalone 'begin' after block declaration.")
        return indent(l:lnum)
      else
        call Debug("Indenting a single line block.")
        return indent(l:lnum) + l:offset
      endif
    elseif l:curr_line =~ '^else' &&
          \ l:line =~ '\<\(if\|assert\)\>\s*(.*)' &&
          \ l:context_level == 0
      call Debug("'else' of 'if' or 'assert'.")
      return indent(l:lnum)
    endif

    if l:context_level < 0
      call Debug("Inside a block.")
      return indent(l:lnum) + l:offset
    elseif l:line =~ s:vlog_context_start
      if l:line =~ s:vlog_module
        call Debug("Inside a module.")
        return indent(l:lnum) + s:indent_modules
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

function! Debug(msg)
  if s:vverb
    echom a:msg
  endif
endfunction

" vi: sw=2 sts=2:
