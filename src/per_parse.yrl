% Copuright (c) 2024 Groupoid Infinity
file -> 'module' id 'do' content : {module,'$2','$4'} .
content -> '$empty' : [] .
content -> line content : ['$1'|'$2'] .
line -> 'import' id : {import,'$2'} .
line -> 'def' id tele ':' exp ':=' exp : {def,'$2','$5','$3','$7'} .
tele -> '$empty' : [] .
tele -> optic tele: ['$1'|'$2'] .
optic -> '(' vars ':' exp ')' : {'()','$2','$4'} .
vars -> id : '$1' .
vars -> id vars : ['$1'|'$2'] .
exp -> id : '$1' .
exp -> id '.' exp : {'.','$1','$3'} .
exp -> exp exp : {app,'$1','$2'} .
exp -> '(' exp ')' : '$2' .
exp -> forall tele ',' exp : {'Π','$2','$4'} .
exp -> sigma tele ',' exp : {'Σ','$2','$4'} .
exp -> exp arrow exp : {'→','$1','$3'} .
exp -> lam tele ',' exp : {'λ','$2','$4'} .
exp -> '?' : {hole} .
exp -> U : {'U'} .
exp -> app : '$1' .
exp -> 'inductive' '{' sum '}' : {inductive,lists:flatten(uncons('$3'))} .
constructor -> id tele : {ctor,'$1','$2'} .
constructor -> id tele ':' exp : {ctor,'$1','$2','$4'} .
sum -> '$empty' : [] .
sum -> constructor : '$1' .
sum -> constructor '|' sum : ['$3'|'$1'] .
app -> exp exp : {app,'$1','$2'} .
Rootsymbol file .
Nonterminals file vars optic content tele exp app line sum constructor .
Terminals id lam arrow forall sigma 'def' 'do' 'U' 'module' 'inductive' 'import' '|' '.' ',' '(' ')' '<' '>' '[' ']' '{' '}' '?' ':=' ':' .
Left 100 app .
Left 10 tele .
Right 10 exp .
Erlang code .
uncons([H|T]) -> [T|uncons(H)] ; uncons(X) -> [X].
