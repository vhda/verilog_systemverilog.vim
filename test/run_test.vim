function! TestFold()
    let fail = 0
    let fail_lines = ''
    let linenr = 0
    while linenr < line("$")
        let linenr += 1
        let line = getline(linenr)
        let linelvl = substitute(line, '.*<\(\d*\)>.*', '\1', '')
        let level = foldlevel(linenr)
        if (level != linelvl)
            let fail = 1
            if (fail_lines == '')
                let fail_lines = linenr
            else
                let fail_lines = fail_lines.','.linenr
            endif
        endif
    endwhile

    if (fail == 1)
        echo 'Fold test failed:'
        echo 'g:verilog_syntax_fold: ' . g:verilog_syntax_fold
        echo fail_lines
        return 1
    else
        echo 'Fold test passed'
        return 0
    endif

endfunction

"-----------------------------------------------------------------------
" Run tests
"-----------------------------------------------------------------------
unlet! g:verilog_dont_deindent_eos
let test_result=0

"-----------------------------------------------------------------------
" Syntax folding test
"-----------------------------------------------------------------------
" Enable all syntax folding
let g:verilog_syntax_fold="all"
set foldmethod=syntax

" Open syntax fold test file in read-only mode
view test/folding.v

" Verify folding
let test_result=test_result || TestFold()
echo ''

"-----------------------------------------------------------------------
" Check test results and exit accordingly
"-----------------------------------------------------------------------
if test_result
  cquit
else
  quit
endif
