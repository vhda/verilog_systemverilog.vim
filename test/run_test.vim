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

function! TestIndent()
    let fail = 0
    let fail_lines = ''
    let linenr = 0
    while linenr < line("$")
        let linenr += 1
        let line = getline(linenr)
        let ind1 = indent(linenr)
        execute 'normal! '.linenr.'gg=='
        let ind2 = indent(linenr)
        if ind1 != ind2
            " Indent has changed so u will undo this.
            execute 'normal! u'
            let fail = 1
            if (fail_lines == '')
                let fail_lines = linenr
            else
                let fail_lines = fail_lines.','.linenr
            endif
        endif
    endwhile

    if (fail == 1)
        echo 'Indent test failed:'
        echo fail_lines
        return 1
    else
        echo 'Indent test passed'
        return 0
    endif

endfunction
"-----------------------------------------------------------------------
" Run tests
"-----------------------------------------------------------------------
let test_result=0

"-----------------------------------------------------------------------
" Syntax folding test
"-----------------------------------------------------------------------
" Enable all syntax folding
let g:verilog_syntax_fold="all"
set foldmethod=syntax
set noautochdir

" Open syntax fold test file in read-only mode
view test/folding.v

" Verify folding
let test_result=test_result || TestFold()
echo ''

"-----------------------------------------------------------------------
" Syntax indent test
"-----------------------------------------------------------------------
" Open syntax indent test file in read-only mode
edit test/indent.sv

" Verify folding
let test_result=test_result || TestIndent()
echo ''

"-----------------------------------------------------------------------
" Check test results and exit accordingly
"-----------------------------------------------------------------------
if test_result
  cquit
else
  quit
endif
