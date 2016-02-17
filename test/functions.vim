function! TestFold(...)
    let fail = 0
    let fail_lines = ''
    let linenr = 0
    if exists("a:1")
        let index = a:1
    else
        let index = 0
    endif
    while linenr < line("$")
        let linenr += 1
        let line = getline(linenr)
        let levels = substitute(line, '.\{-}<\(\d*\)>', '\1::', 'g')
        let levels_list = split(levels, '::')
        " Skip commented out lines
        if line =~ '^\/\/'
            continue
        " Check if requested index is NOT available in the levels list
        elseif index < 0 || (index >= len(levels_list))
            echo 'Invalid line format:'
            echo line
            return 1
        else
            " Store expected indent level
            let level_expected=levels_list[index]
        endif
        " Check indent level
        let level = foldlevel(linenr)
        if (level != level_expected)
            let fail = 1
            echo "Error: level=" . level . " level_expected=" . level_expected . " >>>>" . line
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

