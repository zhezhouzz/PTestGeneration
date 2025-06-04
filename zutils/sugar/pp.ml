open SugarAux

let mk_colored color str = spf " @{<%s>%s@}" color str
let mk_red = mk_colored "red"
let mk_blue = mk_colored "blue"
let printf = Spectrum.Simple.printf
let printfBold boldstr str = Spectrum.Simple.printf "@{<bold>%s@}%s" boldstr str
