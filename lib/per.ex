defmodule Per do

  def file(f) do
      case :file.read_file(f) do
      {:ok,b} -> {:ok,:unicode.characters_to_list(b)}
      {:error,e} -> :io.format(:lists.concat(['File ',f, ' : ',e,'~n']))
                    {:error,:file} end end

  def lexer({:error,s}) do {:error,s} end
  def lexer({:ok,s}) do
      case :per_lex.string(s) do
      {:ok,t,_} -> {:ok,t}
      {:error,{l,a,x},_} -> :io.format(:lists.concat(['Line ',l,' ',a,' : ',:erlang.element(2,x),'~n']))
                    {:error,:lexer} end end

  def parser({:error,t}) do {:error,t} end
  def parser({:ok,t}) do
      case :per_parse.parse(t) do
      {:ok,ast} -> {:ok,ast};
      {:error,{l,a,s}} -> :io.format(:lists.concat(['Line ', l, ' ', a, ' : ', s,'~n']))
                          {:error,:parser} end end

  def parse(f), do: snd(parser(lexer({:ok,f})))
  def a(f), do: snd(parser(lexer(file(f))))

  def fst({x,_}), do: x
  def snd({:error,x}), do: {:error,x}
  def snd({_,[x]}), do: x
  def snd({_,x}), do: x

end
