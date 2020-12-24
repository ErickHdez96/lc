" Vim syntax file
" Language: Tiger
" Maintainer: Erick Hernandez Curiel
" Latest Revision: 2020-05-17

if exists("b:current_syntax")
	finish
endif

" keywords
syn keyword lcKeyword let in letrec type as fix
syn keyword lcConditional if then else case of
syn keyword lcConstant true false unit cons head tail nil isnil
syn keyword lcType Bool Nat Unit List

syn match lcLambda 'λ'
syn match lcLambda '\\'
syn match lcInteger '\d\+'

hi def link lcKeyword Keyword
hi def link lcConditional Conditional
hi def link lcInteger Number
hi def link lcLambda Special
hi def link lcConstant Constant
hi def link lcType Type

let b:current_syntax = "lc"
