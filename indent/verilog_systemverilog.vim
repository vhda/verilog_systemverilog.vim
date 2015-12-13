" Language:     Verilog/SystemVerilog HDL
"
" Credits:
"   Originally created by
"       Chih-Tsun Huang <cthuang@larc.ee.nthu.edu.tw>
" 	http://larc.ee.nthu.edu.tw/~cthuang/vim/indent/verilog.vim
"   Suggestions for improvement, bug reports by
"     Leo Butlero <lbutler@brocade.com>
"   Last maintainer: Amit Sethi <amitrajsethi@yahoo.com>
"
" Buffer Variables:
"     b:verilog_indent_modules : indenting after the declaration
"				 of module blocks
"     b:verilog_indent_width   : indenting width
"     b:verilog_indent_verbose : verbose to each indenting
"
" Revision Comments:
"     Amit Sethi - Wed Jun 28 18:20:44 IST 2006
"       Added SystemVerilog specific indentations
"     Amit Sethi - Thu Jul 27 12:09:48 IST 2006
"       Changed conflicting function name
"

" Only load this indent file when no other was loaded.
if exists("b:did_indent")
  finish
endif
let b:did_indent = 1

setlocal indentexpr=GetVerilog_SystemVerilogIndent()
setlocal indentkeys=!^F,o,O,0),0},=begin,=end,=join,=endcase,=join_any,=join_none
setlocal indentkeys+==endmodule,=endfunction,=endtask,=endspecify
setlocal indentkeys+==endclass,=endpackage,=endsequence,=endclocking
setlocal indentkeys+==endinterface,=endgroup,=endprogram,=endproperty
setlocal indentkeys+==`else,=`endif
setlocal indentkeys+==else

let s:vlog_pre_label         = '^\(\k\w*\s*:\s*\)'
let s:vlog_post_label        = '\(\s*:\s*\k\w*$\)'
let s:vlog_openstat          = '\(\<or\>\|\([*/]\)\@<![*(,{><+-/%^&|!=?:]\([*/]\)\@!\)'
let s:vlog_comment           = '\(//.*\|/\*.*\*/\)'
let s:vlog_block_delcaration = '\(\(if\|foreach\|assert\|for\)\s*(.*)\)\|else'
let s:vlog_stop_condition    = '\(function\|task\|always\|initial\|final\)'
let s:vlog_macro             = '`\k\+\((.*)\)\?$'
let s:vlog_statement         = '.*;$\|'. s:vlog_macro
let s:vlog_assert            = s:vlog_pre_label . '\?\<assert\>\(\s\+property\)\?\s*(.*)' . s:vlog_post_label . '\?'

" Only define the function once.
if exists("*GetVerilog_SystemVerilogIndent")
  finish
endif

set cpo-=C

function! GetVerilog_SystemVerilogIndent()

  if exists('b:verilog_s:indent_modules')
    let s:indent_modules = s:offset
  else
    let s:indent_modules = 0
  endif

  if exists('b:verilog_indent_verbose')
    let s:vverb = 1
  else
    let s:vverb = 0
  endif

  if exists('b:verilog_indent_width')
    let s:offset = b:verilog_indent_width
  else
    let s:offset = &sw
  endif

  " Find a non-blank line above the current line.
  let l:lnum = prevnonblank(v:lnum - 1)

  " At the start of the file use zero indent.
  if l:lnum == 0
    return 0
  endif

  let l:lnum2      = prevnonblank(l:lnum - 1)
  let l:curr_line  = StripCommentsAndWS(getline(v:lnum))
  let l:last_line  = StripCommentsAndWS(getline(l:lnum))
  let l:last_line2 = StripCommentsAndWS(getline(l:lnum2))
  let l:ind        = indent(l:lnum)

  " Get new context line if it is fully commented out
  while l:last_line2 =~ '^\s*'.s:vlog_comment.'\s*$'
    let l:lnum2 = prevnonblank(l:lnum2 - 1)
    let l:last_line2 = StripCommentsAndWS(getline(l:lnum2))
  endwhile

  " Check if inside a comment
  if synIDattr(synID(v:lnum, 1, 0), "name") == "verilogComment"
    if s:vverb
      echom "In comment, returning same indent"
    endif
    return l:ind
  endif

  " Indent after if/else/for/case/always/initial/specify/fork blocks
  if l:last_line =~ '^\(`\@<!\<\(if\|else\)\>\)' ||
   \ l:last_line =~ '^\<\(for\|while\|case\%[[zx]]\|do\|foreach\|randcase\)\>' ||
   \ l:last_line =~ '^\<\(always\|always_comb\|always_ff\|always_latch\)\>' ||
   \ l:last_line =~ '^\<\(initial\|specify\|fork\|final\)\>' ||
   \ l:last_line =~ '^\(\w\+\s*:\s*\)\?\<\(assume\|cover\)\>' ||
   \ l:last_line =~ s:vlog_assert
    if l:last_line !~ '\<end\>$' && 
     \ l:last_line !~ s:vlog_statement ||
     \ l:last_line =~ '\(//\|/\*\).*\(;\|\<end\>\)$'
      let l:ind = l:ind + s:offset
      if s:vverb
        echom "Indent after a block statement:"
        echom l:last_line
      endif
    endif
  " Indent after function/task/class/package/sequence/clocking/
  " interface/covergroup/property/program blocks
  elseif l:last_line =~ '^\(\<\(virtual\|static\|protected\|local\)\>\s\+\)\?\<\(function\|task\)\>' ||
       \ l:last_line =~ '^\(\<virtual\>\s\+\)\?\<\(class\|package\)\>' ||
       \ l:last_line =~ '^\<\(sequence\|clocking\|interface\)\>' ||
       \ l:last_line =~ '^\(\w\+\s*:\)\=\s*\<covergroup\>' ||
       \ l:last_line =~ '^\<\(property\|program\)\>'
    if l:last_line !~ '\<end\>$' ||
     \ l:last_line =~ '\(//\|/\*\).*\(;\|\<end\>\)$'
      let l:ind = l:ind + s:offset
      if s:vverb
        echom "Indent after function/task/class block statement:"
        echom l:last_line
      endif
    endif

  " Indent after module/function/task/specify/fork blocks
  elseif l:last_line =~ '^\(\<extern\>\s*\)\=\<module\>'
    let l:ind = l:ind + s:indent_modules
    if s:vverb && s:indent_modules
      echom "Indent after module statement."
    endif
    if l:last_line =~ '[(,]$' &&
     \ l:last_line !~ '\(//\|/\*\).*[(,]$'
      let l:ind = l:ind + s:offset
      if s:vverb
        echom "Indent after a multiple-line module statement:"
        echom l:last_line
      endif
    endif

  " Indent after a 'begin' statement
  elseif l:last_line =~ '\(\<begin\>\)\(\s*:\s*\w\+\)*$' &&
       \ l:last_line !~ '\(//\|/\*\).*\(\<begin\>\)' &&
       \ ( l:last_line2 !~ s:vlog_openstat . '$' ||
       \ l:last_line2 =~ '^[^=!]\+\s*:$' )
    let l:ind = l:ind + s:offset
    if s:vverb
      echom "Indent after begin statement:"
      echom l:last_line
    endif

  " Indent after a '{' or a '('
  elseif l:last_line =~ '[{(]$' &&
       \ l:last_line !~ '\(//\|/\*\).*[{(]' &&
       \ ( l:last_line2 !~ s:vlog_openstat . '$' ||
       \ l:last_line2 =~ '^[^=!]\+\s*:$' )
    let l:ind = l:ind + s:offset
    if s:vverb
      echom "Indent after begin statement:"
      echom l:last_line
    endif
  elseif l:curr_line !~ 'else' && l:curr_line !~ '^`\(ifdef\|elsif\|endif\)' &&
       \ ( l:last_line =~ '^end$' ||
       \ l:last_line =~ s:vlog_statement && 
       \ l:last_line2 =~ s:vlog_block_delcaration )
    let l:ind = DeindentAfterNested(l:ind, v:lnum)

  " De-indent for the end of one-line block
  " Only de-indents if last line was an end of statement that ended with ;
  " or if it starts with a `define call, which might not require the ; end
  elseif l:last_line =~ s:vlog_statement &&
       \ l:last_line2 =~ '\<\(`\@<!if\|`\@<!else\|for\|while\|always\|initial\|do\|foreach\|final\)\>\(\s*(.*)\)\?$' &&
       \ l:last_line2 !~ '\(//\|/\*\).*\<\(`\@<!if\|`\@<!else\|for\|while\|always\|initial\|do\|foreach\|final\)\>' &&
       \ ( l:last_line2 !~ '\<\(begin\|assert\)\>' || l:last_line2 =~ '\(//\|/\*\).*\<\(begin\|assert\)\>' )
    let l:ind = l:ind - s:offset
    if s:vverb
      echom "De-indent after the end of one-line statement:"
      echom l:last_line2
    endif

  " Multiple-line statement (including case statement)
  " Open statement
  "   Ident the first open line
  elseif  l:last_line =~ s:vlog_openstat . '$' &&
        \ l:last_line !~ '\(//\|/\*\).*' . s:vlog_openstat . '$' &&
        \ l:last_line2 !~ s:vlog_openstat . '$'
    let l:ind = l:ind + s:offset
    if s:vverb
      echom "Indent after an open statement:"
      echom l:last_line
    endif

  " Close statement
  "   De-indent for an optional close parenthesis and a semicolon, and only
  "   if there exists precedent non-whitespace char
  "   Always de-indent if a close parenthesis and a semicolon are
  "   found alone in the previous line
  elseif l:last_line =~ ')\s*;$' &&
       \ l:last_line !~ '\(//\|/\*\).*\S)*\s*;$' &&
       \ ( l:last_line2 =~ s:vlog_openstat . '$' &&
       \ l:last_line2 !~ ';\s*//.*$') &&
       \ l:last_line2 !~ s:vlog_comment ||
       \ l:last_line =~ '^);'
    let l:ind = l:ind - s:offset
    if s:vverb
      echom "De-indent after a close statement:"
      echom l:last_line
    endif

    " Close bracket
    "   Also de-indents a close bracket when preceded by a semicolon, but only
    "   if it is not commented out or alone in a line.
    "   "with" statements are treated exceptionally.
  elseif l:last_line =~ ';\s*}' &&
       \ ( l:last_line !~ '{[^}]\+}' || l:last_line =~ '}\s*)\s*;') &&
       \ l:last_line !~ s:vlog_comment &&
       \ l:last_line !~ '^}' &&
       \ l:last_line !~ '\<with\s*{'
    let l:ind = l:ind - s:offset
    if s:vverb
      echom "De-indent after a closing bracket:"
      echom l:last_line
    endif

    " `ifdef , `ifndef , `elsif , or `else
  elseif l:last_line =~ '^`\<\(ifdef\|ifndef\|elsif\|else\)\>'
    let l:ind = l:ind + s:offset
    if s:vverb
      echom "Indent after a `ifdef , `ifndef , `elsif or `else statement."
      echom l:last_line
    endif
  endif

  if l:curr_line =~ '^endfunction'
    let l:ind = SearchBackForContextStart('function', l:lnum)

  " Re-indent current line

  " De-indent on the end of the block
  " join/end/endcase/endfunction/endtask/endspecify
  elseif l:curr_line =~ '^\<\(join\|join_any\|join_none\|end\|endcase\)\>' ||
       \ l:curr_line =~ '^\<\(endfunction\|endtask\|endspecify\|endclass\)\>' ||
       \ l:curr_line =~ '^\<\(endpackage\|endsequence\|endclocking\|endinterface\)\>' ||
       \ l:curr_line =~ '^\<\(endgroup\|endproperty\|endprogram\)\>' ||
       \ l:curr_line =~ '^}'
    let l:ind = l:ind - s:offset
    if s:vverb
      echom "De-indent the end of a block:"
      echom l:curr_line
    endif

  elseif l:curr_line =~ '^\<endmodule\>'
    if exists("g:verilog_dont_deindent_eos")
      let l:ind = l:ind - s:offset
    else
      let l:ind = l:ind - s:indent_modules
    endif
    if s:vverb && s:indent_modules
      echom "De-indent the end of a module:"
      echom l:curr_line
    endif

  " De-indent else of assert
  elseif l:curr_line =~ '\<else\>' &&
       \ l:curr_line !~ s:vlog_assert &&
       \ l:last_line =~ s:vlog_assert
    let l:ind = l:ind - s:offset
    if s:vverb
      echom "De-indent else of assert"
      echom l:curr_line
    endif

  " De-indent on a stand-alone 'begin'
  elseif l:curr_line =~ '^\<begin\>'
    if l:last_line !~ '^\<\(fork\)\>' &&
     \ l:last_line !~ '^\<\(function\|task\|specify\|module\|class\|package\)\>' &&
     \ l:last_line !~ '^\<\(sequence\|clocking\|interface\|covergroup\)\>'  &&
     \ l:last_line !~ '^\<\(property\|program\)\>' &&
     \ l:last_line !~ '^\()*\s*;\|)\+\)$' && (
     \ l:last_line =~ '\<\(`\@<!if\|`\@<!else\|for\|while\|case\%[[zx]]\|always\|initial\|do\|foreach\|randcase\|final\)\>' ||
     \ l:last_line =~ ')$' ||
     \ l:last_line =~ s:vlog_openstat . '$' )
      let l:ind = l:ind - s:offset
      if s:vverb
        echom "De-indent a stand alone begin statement:"
        echom l:last_line
      endif
    endif

  " De-indent at the end of multiple-line statement
  elseif !exists("g:verilog_dont_deindent_eos") &&
       \ l:curr_line =~ '^);\?' &&
       \ ( l:last_line =~ s:vlog_openstat . '$' ||
       \ l:last_line !~ s:vlog_openstat . '$' &&
       \ l:last_line2 =~ s:vlog_openstat . '$' )
    let l:ind = l:ind - s:offset
    if s:vverb
      echom "De-indent at the end of a multiple statement:"
      echom l:last_line
    endif

  " De-indent `else , `elsif , or `endif
  elseif l:curr_line =~ '^`\<\(else\|elsif\|endif\)\>'
    let l:ind = l:ind - s:offset
    if s:vverb
      echom "De-indent `else , `elsif , or `endif statement:"
      echom l:curr_line
    endif

  endif

  " Return the indention
  return l:ind
endfunction

function! StripCommentsAndWS(line)
  let l:temp = a:line
  if l:temp !~ '^\s*'.s:vlog_comment.'\s*$'
    let l:temp = substitute(l:temp, '//.*', '', 'g')
    let l:temp = substitute(l:temp, '/\*.\{-}\*/', '', 'g')
  endif
  let l:temp = substitute(l:temp, '\s*$', '', 'g')
  let l:temp = substitute(l:temp, '^\s*', '', 'g')
  return l:temp
endfunction

function! SearchBackForContextStart(keyword, current_line_no)
  let l:lnum = a:current_line_no
  let l:iteration = 0
  while 1
    if l:iteration == 100
      " Timeout
      return l:lnum
    else 
      let l:iteration += 1
    endif
    let l:lnum = prevnonblank(l:lnum - 1)
    let l:last_line = StripCommentsAndWS(getline(l:lnum))
    if l:last_line =~ a:keyword 
      return indent(l:lnum)
    endif
  endwhile
endfunction

function! DeindentAfterNested(current_indent, current_line_no)
  let l:ignore_begin = 0
  let l:lnum = a:current_line_no
  let l:iteration = 0

  while 1

    if l:iteration == 100
      " Timeout
      return l:lnum
    else 
      let l:iteration += 1
    endif

    let l:lnum = prevnonblank(l:lnum - 1)
    let l:last_line = StripCommentsAndWS(getline(l:lnum))
    " echom "DEBUG: line: ". l:lnum . ': ' . l:last_line

    if l:last_line =~ 'end$'
      let l:ignore_begin += 1
    elseif l:last_line =~ '\<end\>.*\<begin\>'
      " do nothing
    elseif l:last_line =~ s:vlog_stop_condition
      return indent(l:lnum) + s:offset
    elseif l:last_line =~ '\<begin\>$'
      if l:ignore_begin == 0
        return indent(l:lnum) + s:offset
      else
        let l:ignore_begin -= 1
      endif
    endif

  endwhile
endfunction

" vi: sw=2 sts=2:
