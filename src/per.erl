-module(per).
-description('Per: MLTT').
-behaviour(supervisor).
-behaviour(application).
-export([init/1, start/2, stop/1, start/0, boot/0, tables/0 ]).

opt()        -> [ set, named_table, { keypos, 1 }, public ].
tables()     -> [ term, norm, type, erased, filesystem ].
boot()       -> [ ets:new(T,opt()) || T <- tables() ].
unicode()    -> io:setopts(standard_io, [{encoding, unicode}]).
start()      -> start(normal,[]).
start(_,_)   -> unicode(), supervisor:start_link({local,per},per,[]).
ets_clear()  -> [ ets:delete(T) || T <- tables() ].
stop(_)      -> ets_clear(), ok.
init([])     -> boot(), {ok, {{one_for_one, 5, 10}, []}}.
