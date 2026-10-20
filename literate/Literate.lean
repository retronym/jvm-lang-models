import VersoManual
import Literate.Linking
import Literate.Overriding
import Literate.BinaryCompat
import Literate.Defaults
import Literate.Access
import Literate.Constructors
import Literate.Sealed
import Literate.Linearization
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
The [API documentation](https://retronym.github.io/jvm-lang-models/api/) lists every definition;
the [home page](https://retronym.github.io/jvm-lang-models/) shows the layers and what each can do for you.

{include 1 Literate.Linking}

{include 1 Literate.Overriding}

{include 1 Literate.BinaryCompat}

{include 1 Literate.Defaults}

{include 1 Literate.Access}

{include 1 Literate.Constructors}

{include 1 Literate.Sealed}

{include 1 Literate.Linearization}

{include 1 Literate.ScalaOverriding}
