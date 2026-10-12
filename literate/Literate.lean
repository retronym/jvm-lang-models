import VersoManual
import Literate.Linking
import Literate.Overriding
import Literate.ScalaOverriding

open Verso.Genre Manual

#doc (Manual) "JVM language models, literate" =>
%%%
authors := ["Jason Zaugg"]
shortTitle := "Literate models"
%%%

These pages read the models in [retronym/jvm-lang-models](https://github.com/retronym/jvm-lang-models)
next to the specifications they formalise. Each section quotes the clause it models, shows the
model's definition, and checks an example by evaluation and by the kernel.
The [API documentation](https://retronym.github.io/jvm-lang-models/api/) lists every definition.

{include 1 Literate.Linking}

{include 1 Literate.Overriding}

{include 1 Literate.ScalaOverriding}
