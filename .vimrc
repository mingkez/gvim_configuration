" Vim with all enhancements
source $VIMRUNTIME/vimrc_example.vim

" Use the internal diff if available.
" Otherwise use the special 'diffexpr' for Windows.
if &diffopt !~# 'internal'
  set diffexpr=MyDiff()
endif
function MyDiff()
  let opt = '-a --binary '
  if &diffopt =~ 'icase' | let opt = opt . '-i ' | endif
  if &diffopt =~ 'iwhite' | let opt = opt . '-b ' | endif
  let arg1 = v:fname_in
  if arg1 =~ ' ' | let arg1 = '"' . arg1 . '"' | endif
  let arg1 = substitute(arg1, '!', '\!', 'g')
  let arg2 = v:fname_new
  if arg2 =~ ' ' | let arg2 = '"' . arg2 . '"' | endif
  let arg2 = substitute(arg2, '!', '\!', 'g')
  let arg3 = v:fname_out
  if arg3 =~ ' ' | let arg3 = '"' . arg3 . '"' | endif
  let arg3 = substitute(arg3, '!', '\!', 'g')
  if $VIMRUNTIME =~ ' '
    if &sh =~ '\<cmd'
      if empty(&shellxquote)
        let l:shxq_sav = ''
        set shellxquote&
      endif
      let cmd = '"' . $VIMRUNTIME . '\diff"'
    else
      let cmd = substitute($VIMRUNTIME, ' ', '" ', '') . '\diff"'
    endif
  else
    let cmd = $VIMRUNTIME . '\diff'
  endif
  let cmd = substitute(cmd, '!', '\!', 'g')
  silent execute '!' . cmd . ' ' . opt . arg1 . ' ' . arg2 . ' > ' . arg3
  if exists('l:shxq_sav')
    let &shellxquote=l:shxq_sav
  endif
endfunction

"-----------------------------------------------------------------------------
" base
"-----------------------------------------------------------------------------
" 语法高亮度显示
syntax on
set hlsearch
au BufRead,BufNewfile *.sv set filetype=systemverilog
filetype on                  
set cuc
set cul
" 设置行号
set nu
set noundofile
set nobackup
let mapleader = ","

"防止中文注释乱码
set fileencoding=utf-8
set fenc=utf-8
set fencs=utf-8,usc-bom,euc-jp,gb18030,gbk,gb2312,cp936,big－5                    
set enc=utf-8
let &termencoding=&encoding

" 设置tab4个空格
set tabstop=2
set expandtab

"程序自动缩进时候空格数
set shiftwidth=2

"退格键一次删除4个空格
set softtabstop=2
autocmd FileType make set noexpandtab

" 在编辑过程中，在右下角显示光标位置的状态行
set ruler

" vim使用自动对起，也就是把当前行的对起格式应用到下一行
set autoindent

" 在状态列显示目前所执行的指令
set showcmd
set autochdir "NERDTree dir set
" 设置颜色主题
colorscheme desert
set guifont=Consolas:h14
set nocompatible
set backspace=indent,eol,start

set nocompatible              " 去除VI一致性,必须
" filetype off                  " 必须

au BufReadPost * if line("'\"") > 0|if line("'\"") <= line("$")|exe("norm '\"")|else|exe "norm $"|endif|endif


"-----------------------------------------------------------------------------
"  vundle
"-----------------------------------------------------------------------------
" 设置包括vundle和初始化相关的runtime path
set rtp+=~/.vim/bundle/Vundle.vim
call vundle#begin()
" 另一种选择, 指定一个vundle安装插件的路径
"call vundle#begin('~/some/path/here')

" 让vundle管理插件版本,必须
Plugin 'git://github.com/VundleVim/Vundle.vim'
Plugin 'git://github.com/scrooloose/nerdtree.git'
"Plugin 'git://github.com/w0rp/ale.git'
"Plugin 'git://github.com/bling/vim-airline'
Plugin 'git://github.com/SirVer/ultisnips'
Plugin 'git://github.com/honza/vim-snippets'
Plugin 'git://github.com/Shougo/neocomplcache.vim'
Plugin 'git://github.com/junegunn/vim-easy-align'
Plugin 'git://github.com/scrooloose/nerdcommenter'
Plugin 'derekwyatt/vim-scala'
Plugin 'vhda/verilog_systemverilog.vim'
" 你的所有插件需要在下面这行之前
call vundle#end()            " 必须
filetype plugin on    " 必须 加载vim自带和插件相应的语法和文件类型相关脚本
filetype plugin indent on    " 必须 加载vim自带和插件相应的语法和文件类型相关脚本

" =============================================================
"                        成对标签设置
" =============================================================
source $VIMRUNTIME/macros/matchit.vim

let b:match_ignorecase=0
let b:match_words=
  \ '\<begin\>:\<end\>,' .
  \ '\<if\>:\<else\>,' .
  \ '\<module\>:\<endmodule\>,' .
  \ '\<class\>:\<endclass\>,' .
  \ '\<program\>:\<endprogram\>,' .
  \ '\<clocking\>:\<endclocking\>,' .
  \ '\<property\>:\<endproperty\>,' .
  \ '\<sequence\>:\<endsequence\>,' .
  \ '\<package\>:\<endpackage\>,' .
  \ '\<covergroup\>:\<endgroup\>,' .
  \ '\<primitive\>:\<endprimitive\>,' .
  \ '\<specify\>:\<endspecify\>,' .
  \ '\<generate\>:\<endgenerate\>,' .
  \ '\<interface\>:\<endinterface\>,' .
  \ '\<function\>:\<endfunction\>,' .
  \ '\<task\>:\<endtask\>,' .
  \ '\<for\>:\<endfor\>,' .
  \ '\<while\>:\<endwhile\>,' .
  \ '\<specify\>:\<endspecify\>,' .
  \ '\<generate\>:\<endgenerate\>,' .
  \ '\<case\>\|\<casex\>\|\<casez\>:\<endcase\>,' .
  \ '\<fork\>:\<join\>\|\<join_any\>\|\<join_none\>,' .
  \ '`ifdef\>:`else\>:`endif\>,'
  
:inoremap ( ()<ESC>i
:inoremap [ []<ESC>i
:inoremap { {}<ESC>i
:inoremap " ""<ESC>i

"-----------------------------------------------------------------------------
" NERDTree
"-----------------------------------------------------------------------------
map <leader>ne :NERDTreeToggle<CR>
" 目录树窗口尺寸
let g:NERDTreeWinSize = 25
" 关闭nerd帮助
" let g:NERDTreeMinimalUI = 1
" 忽略以下文件的显示
let NERDTreeIgnore=['\.pyc','\~$','\.swp']
" 显示书签列表
let NERDTreeShowBookmarks=1
" 显示隐藏文件
let NERDTreeShowHidden=1
" 修改默认箭头符号
let g:NERDTreeDirArrowExpandable = '▸'
let g:NERDTreeDirArrowCollapsible = '▾'
augroup NERDTree
    "au!
    "autocmd vimenter * NERDTree     " vim启动时自动打开NERDTree
    " vim启动打开目录时自动打开NERDTree
    "autocmd StdinReadPre * let s:std_in=1
    "autocmd VimEnter * if argc() == 1 && isdirectory(argv()[0]) && !exists("s:std_in") | exe 'NERDTree' argv()[0] | wincmd p | ene | endif
    "autocmd vimenter * NERDTreeFind 
    " 文件全部关闭时退出NERDTree
    autocmd bufenter * if (winnr("$") == 1 && exists("b:NERDTree") && b:NERDTree.isTabTree()) | q | endif
augroup END

map <F2> :NERDTreeMirror<CR>
map <F2> :NERDTreeToggle<CR>

wincmd w
autocmd VimEnter * wincmd w


"-----------------------------------------------------------------------------
" ale.vim
"-----------------------------------------------------------------------------
"keep the sign gutter open
"let g:ale_sign_column_always = 1
"let g:ale_sign_error = '>>'
"let g:ale_sign_warning = '--'
" 
"" show errors or warnings in my statusline
"let g:airline#extensions#ale#enabled = 1
"" self-define statusline
"" use quickfix list instead of the loclist
"let g:ale_set_loclist = 0
"let g:ale_set_quickfix = 1
"" only enable these linters
"let g:ale_linters = {
"\    'verilog': ['verilator']
"\}
"nmap <silent> <C-k> <Plug>(ale_previous_wrap)
"nmap <silent> <C-J> <Plug>(ale_next_wrap)
"" run lint only on saving a file
"" let g:ale_lint_on_text_changed = 'never'
"" dont run lint on opening a file
"" let g:ale_lint_on_enter = 0
"

"-----------------------------------------------------------------------------
"snippet.vim
"-----------------------------------------------------------------------------
let g:UltiSnipsExpandTrigger = "<tab>"
let g:UltiSnipsListSnippets = "<c-tab>"
let g:UltiSnipsJumpForwardTrigger = "<tab>"
let g:UltiSnipsJumpBackwardTrigger = "<s-tab>"



"-----------------------------------------------------------------------------
" neocomplcache
"-----------------------------------------------------------------------------
let g:neocomplcache_enable_auto_select = 1 "作用：提示的时候默认选择地一个，如果你设置为0，每次输入都需要用上下键选择
let g:neocomplcache_disable_auto_complete = 1
"Note: This option must set it in .vimrc(_vimrc).  NOT IN .gvimrc(_gvimrc)!
" Disable AutoComplPop.
let g:acp_enableAtStartup = 0
" Use neocomplcache.
let g:neocomplcache_enable_at_startup = 1
" Use smartcase.
let g:neocomplcache_enable_smart_case = 1
" Set minimum syntax keyword length.
let g:neocomplcache_min_syntax_length = 3
let g:neocomplcache_lock_buffer_name_pattern = '\*ku\*'

" Enable heavy features.
" Use camel case completion.
"let g:neocomplcache_enable_camel_case_completion = 1
" Use underbar completion.
"let g:neocomplcache_enable_underbar_completion = 1

" Define dictionary.
let g:neocomplcache_dictionary_filetype_lists = {
    \ 'default' : '',
    \ 'vimshell' : $HOME.'/.vimshell_hist',
    \ 'scheme' : $HOME.'/.gosh_completions'
        \ }

" Define keyword.
if !exists('g:neocomplcache_keyword_patterns')
    let g:neocomplcache_keyword_patterns = {}
endif
let g:neocomplcache_keyword_patterns['default'] = '\h\w*'

" Plugin key-mappings.
inoremap <expr><C-g>     neocomplcache#undo_completion()
inoremap <expr><C-l>     neocomplcache#complete_common_string()

" Recommended key-mappings.
" <CR>: close popup and save indent.
inoremap <silent> <CR> <C-r>=<SID>my_cr_function()<CR>
function! s:my_cr_function()
  return neocomplcache#smart_close_popup() . "\<CR>"
  " For no inserting <CR> key.
  "return pumvisible() ? neocomplcache#close_popup() : "\<CR>"
endfunction
" <TAB>: completion.
inoremap <expr><TAB>  pumvisible() ? "\<C-n>" : "\<TAB>"
" <C-h>, <BS>: close popup and delete backword char.
inoremap <expr><C-h> neocomplcache#smart_close_popup()."\<C-h>"
inoremap <expr><BS> neocomplcache#smart_close_popup()."\<C-h>"
inoremap <expr><C-y>  neocomplcache#close_popup()
inoremap <expr><C-e>  neocomplcache#cancel_popup()
" Close popup by <Space>.
"inoremap <expr><Space> pumvisible() ? neocomplcache#close_popup() : "\<Space>"

" For cursor moving in insert mode(Not recommended)
"inoremap <expr><Left>  neocomplcache#close_popup() . "\<Left>"
"inoremap <expr><Right> neocomplcache#close_popup() . "\<Right>"
"inoremap <expr><Up>    neocomplcache#close_popup() . "\<Up>"
"inoremap <expr><Down>  neocomplcache#close_popup() . "\<Down>"
" Or set this.
"let g:neocomplcache_enable_cursor_hold_i = 1
" Or set this.
"let g:neocomplcache_enable_insert_char_pre = 1

" AutoComplPop like behavior.
"let g:neocomplcache_enable_auto_select = 1

" Shell like behavior(not recommended).
"set completeopt+=longest
"let g:neocomplcache_enable_auto_select = 1
"let g:neocomplcache_disable_auto_complete = 1
"inoremap <expr><TAB>  pumvisible() ? "\<Down>" : "\<C-x>\<C-u>"

" Enable omni completion.
autocmd FileType css setlocal omnifunc=csscomplete#CompleteCSS
autocmd FileType html,markdown setlocal omnifunc=htmlcomplete#CompleteTags
autocmd FileType javascript setlocal omnifunc=javascriptcomplete#CompleteJS
autocmd FileType python setlocal omnifunc=pythoncomplete#Complete
autocmd FileType xml setlocal omnifunc=xmlcomplete#CompleteTags

" Enable heavy omni completion.
if !exists('g:neocomplcache_force_omni_patterns')
  let g:neocomplcache_force_omni_patterns = {}
endif
let g:neocomplcache_force_omni_patterns.php = '[^. \t]->\h\w*\|\h\w*::'
let g:neocomplcache_force_omni_patterns.c = '[^.[:digit:] *\t]\%(\.\|->\)'
let g:neocomplcache_force_omni_patterns.cpp = '[^.[:digit:] *\t]\%(\.\|->\)\|\h\w*::'

" For perlomni.vim setting.
" https://github.com/c9s/perlomni.vim
let g:neocomplcache_force_omni_patterns.perl = '\h\w*->\h\w*\|\h\w*::'

inoremap <c-r> <c-x><c-u>

"-----------------------------------------------------------------------------
" easyalign
"-----------------------------------------------------------------------------
" Start interactive EasyAlign in visual mode (e.g. vipga)
xmap ga <Plug>(EasyAlign)
" Start interactive EasyAlign for a motion/text object (e.g. gaip)
nmap ga <Plug>(EasyAlign)


"-----------------------------------------------------------------------------
" verilog_inst_gen
"-----------------------------------------------------------------------------
"so ~/.vim/bundle/vlog_inst_gen.vim
"let g:vlog_inst_gen_mode=2 "copy to clipboard and echo inst in split window


"-----------------------------------------------------------------------------
"vtag
"-----------------------------------------------------------------------------
"source /home/eda/vtags-3.01/vtags_vim_api.vim


"-----------------------------------------------------------------------------
"nerdcommenter
"-----------------------------------------------------------------------------
let mapleader = ","
let g:NERDSpaceDelims=1

" verilog_systemverilog
let g:verilog_syntax_fold_lst = "all"
set foldmethod=syntax
autocmd BufNewFile,BufRead *.snippets set ft=snippets
"-----------------------------------------------------------------------------
" Add File Header
"-----------------------------------------------------------------------------
autocmd BufNewFile *.v,*.sv,*.cpp,*.c,*.h exec ":call AddHeader()"
autocmd BufWrite *.v call UpdateLastModifyTime()

function s:GetUserName() 
    let user_name = "mkzheng"
    return user_name
endfunction 

function AddHeader() 
	let line = getline(1)
  	let filename = expand("%")
	call append(0,  "// +FHDR----------------------------------------------------------------------------")
	call append(1,  "//                 Copyright (c) ".strftime("%Y ") )
	call append(2,  "//                       ALL RIGHTS RESERVED")
	call append(3,  "// ---------------------------------------------------------------------------------")
	call append(4,  "// Filename      : ".filename)
	call append(5,  "// Author        : ".s:GetUserName())
	call append(6,  "// Created On    : ".strftime("%Y-%m-%d %H:%M"))
	call append(7,  "// Last Modified : ")
	call append(8,  "// ---------------------------------------------------------------------------------")
	call append(9,  "// Description   : ")
	call append(10, "//")
	call append(11, "//")
	call append(12, "// -FHDR----------------------------------------------------------------------------")
    call append(13, 'module '.expand("%:r")."(")
    call append(14, '')
    call append(15, ');')
    call append(16, '')
    call append(17, '')
    call append(18, 'endmodule')
endfunction 

function AddHeaderfile() 
	let line = getline(1)
  	let filename = expand("%")
	call append(0,  "// +FHDR----------------------------------------------------------------------------")
	call append(1,  "//                 Copyright (c) ".strftime("%Y ") )
	call append(2,  "//                       ALL RIGHTS RESERVED")
	call append(3,  "// ---------------------------------------------------------------------------------")
	call append(4,  "// Filename      : ".filename)
	call append(5,  "// Author        : ".s:GetUserName())
	call append(6,  "// Created On    : ".strftime("%Y-%m-%d %H:%M"))
	call append(7,  "// Last Modified : ")
	call append(8,  "// ---------------------------------------------------------------------------------")
	call append(9,  "// Description   : ")
	call append(10, "//")
	call append(11, "//")
	call append(12, "// -FHDR----------------------------------------------------------------------------")
endfunction 

map <F10>:call AddHeaderfile()<CR>

"-----------------------------------------------------------------------------
" ModifyTime
"-----------------------------------------------------------------------------
function UpdateLastModifyTime() 
	let line = getline(8)
	if line =~ '// Last Modified'
		call setline(8,"// Last Modified : " . strftime("%Y-%m-%d %H:%M"))
	endif
endfunction 


:ab uivs localparam CLK_VALUE = 100;<Enter>initial begin<Enter>clk_i   = 0;<Enter>rst_n_i = 0;<Enter>#10;<Enter>rst_n_i = 1;<Enter>end<Enter>always #CLK_VALUE clk_i = ~clk_i;<Enter>

:ab makefile all:clean elab run verdi<Enter><Enter>elab:<Enter>vcs -full64 -LDFLAGS -Wl,-no-as-needed -nc -l comp_log +v2k \<Enter>-sverilog ../rtl/*.v \<Enter>-sverilog ../tb/*.v \<Enter>-P /opt/verdi/share/PLI/VCS/linux64/novas.tab \<Enter>/opt/verdi/share/PLI/VCS/linux64/pli.a<Enter><Enter>run:<Enter>./simv -l run.log<Enter><Enter>verdi:<Enter>verdi -nologo ../rtl/*.v ../tb/*.v -ssf ./novas.fsdb<Enter><Enter>clean:<Enter>rm -rf AN.DB DVEfiles csrc simv.* *.simv inter.vpd ucli.key ucli.key *_log novas* *fsdb<Enter>

:ab fsdb initial begin<Enter>$fsdbDumpfile("novas.fsdb");<Enter>$fsdbDumpvars;<Enter>$display("Goodjob!!\n");<Enter>end


