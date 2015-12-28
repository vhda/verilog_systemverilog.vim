function! TestFold(...)
    let fail = 0
    let fail_lines = ''
    let linenr = 0
    while linenr < line("$")
        let linenr += 1
        let line = getline(linenr)
        let levels = substitute(line, '.\{-}<\(\d*\)>', '\1,', 'g')
        let levels_list = split(levels, ',')
        if (len(levels_list) > 1 && a:0 > 0)
          let linelvl=levels_list[a:1]
        else
          let linelvl=levels_list[0]
        endif
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

