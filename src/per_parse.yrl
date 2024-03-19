% Copyright Groupoid Infinity, Inc.

mod -> 'module' id 'do' content : {module,'$2','$4'}.
content -> line : '$1'.
content -> line content : ['$1'|'$2'].
ids -> id : '$1'.
ids -> id ids : ['$1'|'$2'].
lense -> '(' ids ':' exp ')' : {tele,'$2','$4'}.
lense -> '[' ids ':' exp ']' : {tele,'$2','$4'}.
lense -> '{' ids ':' exp '}' : {tele,'$2','$4'}.
tele -> lense : '$1'.
tele -> lense tele : ['$1'|'$2'].
exp -> id : '$1'.
exp -> id '.' exp : {field,'$1','$3'}.
exp -> exp exp : {app,'$1','$2'}.
exp -> '(' exp ')' : '$2'.
exp -> lense : '$1'.
exp -> forall params ',' exp : {pi,'$2','$4'}.
exp -> lam params ',' exp : {lam,'$1','$4'}.
exp -> exp arrow exp : {arrow,'$2','$3'}.
exp -> sigma params ',' exp : {sigma,'$2','$4'}.
exp -> '?' : {hole}.
exp -> U : {'U'}.
exp -> V : {'V'}.
exp -> app : '$1'.
app -> exp exp : {app,'$1','$2'}.
params -> '$empty' : [].
params -> tele params : ['$1'|'$2'].
line -> 'import' id : {import,'$2'}.
line -> 'def' id params ':' exp ':=' exp : {def,'$2','$5','$3','$7'}.

Rootsymbol mod.
Nonterminals mod content ids lense tele exp params line app.
Terminals id lam arrow forall sigma 'def' 'do' 'U' 'V' 'module' 'import'
          '.' ',' '(' ')' '[' ']' '{' '}' '?' ':=' ':' .

Left 100 app.
Left 10 tele.
Right 10 exp.

Erlang code.
