import VersoManual
import Literate

open Verso.Genre Manual

def config : Config where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2

def main := manualMain (%doc Literate) (config := { config with })
