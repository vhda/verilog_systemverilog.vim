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
"     b:verilog_indent_modules    : Indentation within module blocks.
"     b:verilog_indent_width      : Indenting width.
"     b:verilog_indent_verbose    : Print debug info for each indent.
"     b:verilog_dont_deindent_eos : Don't de-indent the ); line in port lists
"                                   and instances.
"     b:verilog_indent_preproc    : Indent preprocessor statements.

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

let s:vlog_open_statement = '\(\<or\>\|[<>:!=?&|^%/*+-]\)'
let s:vlog_comment        = '\(//.*\|/\*.*\*/\)'
let s:vlog_macro          = '`\k\+\((.*)\)\?\s*$'
let s:vlog_statement      = '.*;\s*$\|'. s:vlog_macro
let s:vlog_sens_list      = '\(@\s*(.*)\)'
let s:vlog_always         = '\<always\(_ff\|_comb\|_latch\)\?\>\s*' . s:vlog_sens_list . '\?'
let s:vlog_method         = '^\(\s*pure\s\+virtual\|\s*extern\)\@!.*\<\(function\|task\)\>\s\+\(\[.*\]\s*\)\?\w\+'

let s:vlog_block_start    = '\<\(begin\|case\|^\s*fork\)\>\|{\|('
let s:vlog_block_end      = '\<\(end\|endcase\|join\(_all\|_none\)\?\)\>\|}\|)'

let s:vlog_module         = '\<\(extern\s\+\)\@<!module\>'
let s:vlog_class          = '\<\(typedef\s\+\)\@<!class\>'
let s:vlog_property       = '\(\(assert\|assume\|cover\)\s\+\)\@<!\<property\>'
let s:vlog_case           = '\<case[zx]\?\>\s*('
let s:vlog_join           = '\<join\(_all\|_none\)\?\>'

let s:vlog_block_decl     = '\(\<\(while\|if\|foreach\|for\)\>\s*(\)\|\<\(else\|do\)\>\|' . s:vlog_always .'\|'. s:vlog_module

let s:vlog_context_start  = '\<\(package\|covergroup\|program\|sequence\|interface\)\>\|'.
                           \ s:vlog_class .'\|'. s:vlog_property .'\|'.
                           \ s:vlog_method

let s:vlog_context_end    = '\<end\(package\|function\|class\|module\|group\|program\|property\|sequence\|interface\|task\)\>\|`endif\>'

let s:vlog_preproc_start  = '^\s*`ifn\?def\>'
let s:vlog_preproc_end    = '^\s*`endif\>'

" Only define the function once.
if exists("*GetVerilogSystemVerilogIndent")
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

  if s:curr_line =~ '^\s*)'
    let l:extra_offset = 0
    if s:curr_line =~ '^\s*);\s*$' &&
          \ (exists('b:verilog_dont_deindent_eos') ||
          \ exists('g:verilog_dont_deindent_eos'))
      let l:extra_offset = s:offset
    endif
    call s:Verbose("Indenting )")
    return indent(s:SearchForBlockStart('(', '', ')', v:lnum, 0)) + l:extra_offset
  elseif s:curr_line =~ '^\s*}'
    call s:Verbose("Indenting }")
    return indent(s:SearchForBlockStart('{', '', '}', v:lnum, 0))
  endif

  " Reset indent for end blocks.
  if s:curr_line =~ '^\s*\<end'
    if s:curr_line =~ '^\s*\<endfunction\>'
      return indent(s:SearchBackForPattern('\<function\>'  , v:lnum))
    elseif s:curr_line =~ '^\s*\<endtask\>'
      return indent(s:SearchBackForPattern('\<task\>'      , v:lnum))
    elseif s:curr_line =~ '^\s*\<endclocking\>'
      return indent(s:SearchBackForPattern('\<clocking\>'  , v:lnum))
    elseif s:curr_line =~ '^\s*\<endpackage\>'
      return indent(s:SearchBackForPattern('\<package\>'   , v:lnum))
    elseif s:curr_line =~ '^\s*\<endinterface\>'
      return indent(s:SearchBackForPattern('\<interface\>' , v:lnum))
    elseif s:curr_line =~ '^\s*\<endproperty\>'
      return indent(s:SearchBackForPattern('\<property\>'  , v:lnum))
    elseif s:curr_line =~ '^\s*\<endgroup\>'
      return indent(s:SearchBackForPattern('\<covergroup\>', v:lnum))
    elseif s:curr_line =~ '^\s*\<endspecify\>'
      return indent(s:SearchBackForPattern('\<specify\>'   , v:lnum))
    elseif s:curr_line =~ '^\s*\<endsequence\>'
      return indent(s:SearchBackForPattern('\<sequence\>'  , v:lnum))
    elseif s:curr_line =~ '^\s*\<endmodule\>'
      return indent(s:SearchForBlockStart('\<module\>', '', '\<endmodule\>', v:lnum, 0))
    elseif s:curr_line =~ '^\s*\<endclass\>'
      return indent(s:SearchForBlockStart('\<class\>' , '', '\<endclass\>' , v:lnum, 0))
    elseif s:curr_line =~ '^\s*\<end\>'
      return indent(s:SearchForBlockStart('\<begin\>' , '', '\<end\>'      , v:lnum, 1))
    elseif s:curr_line =~ '^\s*\<endcase\>'
      return indent(s:SearchForBlockStart(s:vlog_case , '', '\<endcase\>'  , v:lnum, 0))
    endif
  endif

  if s:curr_line =~ '^\s*\<while\>\s*(.*);'
    return indent(s:SearchForBlockStart('\<do\>', '', '\<while\>\s*(.*);', v:lnum, 1))
  elseif s:curr_line =~ '^\s*`\(endif\|else\|elsif\)\>'
    return indent(s:SearchForBlockStart(s:vlog_preproc_start, '`else\>\|`elsif\>', '`endif\>', v:lnum, 1))
  elseif s:curr_line =~ '^\s*' . s:vlog_join
    return indent(s:SearchForBlockStart('^\s*\<fork\>', '', s:vlog_join, v:lnum, 1))
  endif

  if s:curr_line =~ '^\s*'.s:vlog_comment.'\s*$' &&
        \ getline(v:lnum + 1) =~ '^\s*else'
    return indent(v:lnum + 1)
  endif

  if s:curr_line =~ s:vlog_statement &&
        \ getline(v:lnum - 1) =~ 'else\s*$'
    return indent(v:lnum - 1) + s:offset
  endif

  return s:GetContextIndent()

endfunction

function! s:StripComments(lnum)
  let l:temp = getline(a:lnum)

  " Remove inline comments
  if l:temp !~ '^\s*'.s:vlog_comment.'\s*$'
    let l:temp = substitute(l:temp, '/\*.\{-}\*/\|//.*', '', 'g')
  endif

  return l:temp
endfunction

function! s:SearchBackForPattern(pattern, current_line_no)
  let l:lnum = a:current_line_no

  while l:lnum > 0
    let l:lnum = search(a:pattern, 'bW')
    if getline(l:lnum) !~ s:vlog_comment
      call s:Verbose("Reset indent for context end -> " . a:keyword)
      return l:lnum
    endif
  endwhile

endfunction

" For any kind of block with a provided end pattern and start pattern, return the
" line of the start of the block.
function! s:SearchForBlockStart(start_wd, mid_wd, end_wd, current_line_no, skip_start_end)
  call cursor(a:current_line_no, 1)

  " Detect whether the cursor is on a comment.
  let l:skip_arg = 'synIDattr(synID(".", col("."), 0), "name") == "verilogComment"'

  if a:skip_start_end == 1
    let l:skip_arg =
          \ l:skip_arg." || getline('.') =~ '".a:end_wd.'.\{-}'.a:start_wd."'"
  endif

  let l:lnum = searchpair(a:start_wd, a:mid_wd, a:end_wd, 'bnW', l:skip_arg)
  call s:Verbose('SearchForBlockStart: returning l:lnum ' . l:lnum)
  return l:lnum
endfunction

" Calculates the current line's indent taking into account its context
"
" It checks all lines before the current and when it finds an indenting
" context adds an s:offset to its indent value. Extra indent offset
" related with open statement, for example, are stored in l:extra_offset
" to caculate the final indent value.
function! s:GetContextIndent()
  let l:bracket_level  = 0
  let l:cbracket_level = 0

  let l:lnum = v:lnum
  let l:oneline_mode = 1
  let l:look_for_open_statement = 1
  let l:extra_offset = 0

  " Loop that searches up the file to build a context and determine the correct
  " indentation.
  while l:lnum > 1

    let l:lnum = prevnonblank(l:lnum - 1)
    let l:line = getline(l:lnum)

    " Never use comments to determine indentation.
    if l:line =~ '^\s*' . s:vlog_comment
      continue
    endif

    let l:line = s:StripComments(l:lnum)

    call s:Verbose("GetContextIndent:" . l:lnum . ": " . l:line)

    if l:look_for_open_statement == 1
      if l:line =~ s:vlog_open_statement . '\s*$' &&
            \ l:line !~ '/\*\s*$' && !s:IsComment(l:lnum) ||
            \ s:curr_line =~ '^\s*' . s:vlog_open_statement &&
            \ s:curr_line !~ '^\s*/\*' &&
            \ s:curr_line !~ s:vlog_comment && !s:IsComment(v:lnum)
        let l:extra_offset += s:offset
        call s:Verbose("Increasing indent for an open statment.")
      endif
      let l:look_for_open_statement = 0
    endif

    if l:line =~ '\<begin\>'
      call s:Verbose("Inside a 'begin end' block.")
      return indent(l:lnum) + s:offset + l:extra_offset
    elseif l:line =~ '^\s*\<fork\>'
      call s:Verbose("Inside a 'fork join' block.")
      return indent(l:lnum) + s:offset + l:extra_offset
    elseif l:line =~ s:vlog_case
      call s:Verbose("Inside a 'case' block.")
      return indent(l:lnum) + s:offset + l:extra_offset
    endif

    " If we hit an 'end', 'endcase' or 'join', skip past the whole block.
    if l:line =~ '\<end\>' && l:line !~ '\<begin\>\s*$'
      let l:lnum = s:SearchForBlockStart('\<begin\>', '', '\<end\>', l:lnum, 1)
      let l:oneline_mode = 0
      let l:line = s:StripComments(l:lnum)
    endif

    if l:line =~ s:vlog_join
      let l:lnum = s:SearchForBlockStart('^\s*\<fork\>', '', s:vlog_join, l:lnum, 1)
      let l:oneline_mode = 0
      let l:line = s:StripComments(l:lnum)
    endif

    if l:line =~ '\<endcase\>'
      let l:lnum = s:SearchForBlockStart(s:vlog_case, '', '\<endcase\>', l:lnum, 1)
      let l:oneline_mode = 0
      let l:line = s:StripComments(l:lnum)
    endif

    if l:line =~ '[()]'
      let l:bracket_level +=
            \ s:CountMatches(l:line, ')') - s:CountMatches(l:line, '(')
      if l:bracket_level < 0
        call s:Verbose("Inside a '()' block.")
        return indent(l:lnum) + s:offset + l:extra_offset
      endif
    endif

    if l:line =~ '[{}]'
      let l:cbracket_level +=
            \ s:CountMatches(l:line, '}') - s:CountMatches(l:line, '{')
      if l:cbracket_level < 0
        call s:Verbose("Inside a '{}' block.")
        return indent(l:lnum) + s:offset + l:extra_offset
      endif
    endif

    if l:oneline_mode == 1 && l:line =~ s:vlog_statement
      let l:oneline_mode = 0
    elseif l:oneline_mode == 1 && l:line =~ s:vlog_block_decl
      if s:curr_line =~ '^\s*\<begin\>'
        call s:Verbose("Standalone 'begin' after block declaration.")
        return indent(l:lnum)
      elseif s:curr_line =~ '^\s*{\s*$' && l:cbracket_level == 0
        call s:Verbose("Standalone '{' after block declaration.")
        return indent(l:lnum)
      elseif s:curr_line =~ '^\s*(\s*$' && l:bracket_level == 0
        call s:Verbose("Standalone '(' after block declaration.")
        return indent(l:lnum)
      else
        call s:Verbose("Indenting a single line block.")
        return indent(l:lnum) + s:offset + l:extra_offset
      endif
    elseif s:curr_line =~ '^\s*else' && l:line =~ '\<\(if\|assert\)\>\s*(.*)'
      call s:Verbose("'else' of 'if' or 'assert'.")
      return indent(l:lnum)
    endif

    if l:line =~ s:vlog_module
      call s:Verbose("Inside a module.")
      if !exists('b:verilog_indent_modules') || b:verilog_indent_modules == 0
        return indent(l:lnum) + l:extra_offset
      else
        return indent(l:lnum) + s:offset + l:extra_offset
      endif
    elseif l:line =~ s:vlog_preproc_start
      if exists('b:verilog_indent_preproc') && b:verilog_indent_preproc == 1
        call s:Verbose("After preproc start.")
        return indent(l:lnum) + s:offset + l:extra_offset
      endif
    elseif l:line =~ s:vlog_context_start
      call s:Verbose("Inside a context (".l:lnum.":".l:extra_offset.")")
      return indent(l:lnum) + s:offset + l:extra_offset
    elseif l:line =~ s:vlog_context_end
      if l:line =~ s:vlog_preproc_end
        if exists('b:verilog_indent_preproc')
          call s:Verbose("After preproc end.")
          return indent(l:lnum) + l:extra_offset
        endif
      else
        call s:Verbose("After the end of a context.")
        return indent(l:lnum)
      endif
    endif

  endwhile

  " Return any calculated extra offset if no indenting context was found
  return l:extra_offset
endfunction

function! s:CountMatches(line, pattern)
  return len(split(a:line, a:pattern, 1)) - 1
endfunction

function! s:Verbose(msg)
  if s:vverb
    echom a:msg
  endif
endfunction

function! s:IsComment(lnum)
  return synIDattr(synID(a:lnum, 1, 0), "name") == "verilogComment"
endfunction

" vi: sw=2 sts=2:
