import VersoManual
import Literate

open Verso.Genre Manual
open Verso.Output.Html

def config : Config where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  -- Verso's styles are light only; without this a dark browser theme gives dark text on dark.
  extraHead := #[{{<meta name="color-scheme" content="light"/>}},
    {{<style>"html { background: #fff; color: #000; }"</style>}}]

def main := manualMain (%doc Literate) (config := { config with })
