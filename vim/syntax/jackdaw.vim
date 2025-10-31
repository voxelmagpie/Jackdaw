syntax match jdComment "//.*$"
syntax region jdString start=/"/ skip=/\\"/ end=/"/ oneline
syntax region jdChar start=/'/ skip=/\\'/ end=/'/ oneline
syntax keyword jdKeywords if else type enum struct union var fn accessor iterator const alias loop break continue ref in return true false void nullptr as for foreach and or yield require uninitialised match import unsafe throw try catch borrow
syntax match jdType "\v<[A-Z][a-zA-Z0-9_]*>"
syntax match jdAttributes "\v\@[A-Z][a-zA-Z0-9_]*"
syntax match jdNumber "\v<\d+(\.\d+)?>"
syntax match jdNumber "\v<0x\x+>"
syntax match jdNumber "\v<0b[01]+>"

highlight default link jdComment Comment
highlight default link jdString String
highlight default link jdChar String
highlight default link jdKeywords Keyword
highlight default link jdType Type
highlight default link jdNumber Number
highlight default link jdAttributes PreProc