% Copyright Groupoid Infinity, Inc.

Definitions.

A = [\*\'a-zA-Z_0-9\-\x{B2}-\x{B3}\x{B9}\x{2070}-\x{2071}\x{2080}-\x{2089}\x{2090}-\x{209C}\x{2074}-\x{208E}\x{2010}-\x{2191}\x{2193}-\x{2199}\x{2201}-\x{25FF}\x{3B1}-\x{3BA}\x{3BC}-\x{3FF}\/\;\x{3A0}-\x{3AF}\x{80}-\x{FF}\x{2B0}-\x{2EF}\x{390}-\x{39F}\x{21A0}-\x{21FF}\x{1D40}-\x{1D4F}\x{3000}-\x{301F}\x{1D7C0}-\x{1D7CF}\x{2600}-\x{261F}\x{2200}-\x{221F}]
S = ([\t\s\r\n]|--.*)
B = [\r\n]
Slash   = \\
Dot     = \.
Comma   = \,
Sigma   = (\x{CE}\x{A3}|\Σ)
Arrow   = (\-\>|\→)
Forall  = (\\/|\x{CE}\x{A0}|\П|\Π)
Meet    = (/\\)
Lambda  = (\\|\λ)
Curly   = [\{\}]
Angle   = [\<\>]
Parens  = [\(\)]
Square  = [\[\]]
Colon   = \:
Semicolon = \;
Et      = \@
Eq      = \=
Assign  = \:=
Pipe    = \|

Rules.

(def|inductive|do|end|import|module|U) : {token,{list_to_atom(TokenChars),TokenLine}}.
({Curly}|{Parens}|{Angle}|{Square}|{Colon}) : {token,{list_to_atom(TokenChars),TokenLine}}.
({Dot}||{Comma}|{Eq}|{Assign}|{Colon}|{Semicolon}|{Pipe}|{Et}) : {token,{list_to_atom(TokenChars),TokenLine}}.
{Arrow} : {token, {arrow, TokenLine}}.
{Forall} : {token, {forall, TokenLine}}.
{Meet} : {token, {meet, TokenLine}}.
{Sigma} : {token, {sigma, TokenLine}}.
{Lambda} : {token, {lam, TokenLine}}.
{A}+ : {token, {id, TokenLine, unicode:characters_to_binary(TokenChars)}}.
{B}+ : skip_token.
{S}+ : skip_token.

Erlang code.
