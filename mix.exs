defmodule Per.Mixfile do
  use Mix.Project
  def project do
    [ app: :per,
      version: "1.0.0",
      elixir: ">= 1.9.0",
      description: "Groupoid Infinity Per Programming Language",
      compilers: [:leex,:yecc] ++ Mix.compilers(),
      deps: deps(),
      package: package(),
    ]
  end
  def package do
    [ files: ["lib", "src", "priv", "mix.exs", "CNAME", "LICENSE"],
      maintainers: ["Namdak Tonpa"],
      licenses: ["ISC"],
      links: %{"GitHub" => "https://github.com/groupoid/per"}
    ]
  end
  def application do
    [ extra_applications: [],
      mod: {:per,[]}
    ]
  end
  def deps do
    [
      {:ex_doc, "~> 0.21", only: :dev}
    ]
  end
end
