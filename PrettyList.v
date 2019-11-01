Load Doc.
Load formatList.

Fixpoint docToVar (doc: Doc): t':=
  match doc with
  | Text s     => constructDoc s
  | Indent n d => indentDoc n (docToVar d)
  | Beside a b => besideDoc (docToVar a) (docToVar b)
  | Above a b  => aboveDoc (docToVar a) (docToVar b)
  | Choice a b => choiceDoc (docToVar a) (docToVar b)
  | Fill a b n => fillDoc (docToVar a) (docToVar b) n
  end.

(* width you can set in 'default_width'*)
Definition pretty (doc: Doc): string :=
  to_string' (docToVar doc).