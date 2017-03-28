Require Import ListSet.

Module SPL.

  Parameter FM: Set.
  Parameter Configuration: Set.

  Variable fm_semantics: FM -> set Configuration.

  Notation "[| fm |]" := (fm_semantics fm) :SPL_scope.

End SPL.