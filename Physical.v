Require Import Pig.Base.

Module Physical.

Inductive tm: Type :=
 | t_filter: id -> id -> tm
 | t_foreach: id -> id -> tm 
 | t_lrearrange: id -> col -> tm
 | t_grearrange: id -> col -> tm
 | t_package : id -> col -> tm
 | t_load: id -> ty -> tm
 | t_assign: id -> tm -> tm
 | t_store: id -> tm
 | t_seq: tm -> tm -> tm.



Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=

  | T_Filter : forall Gamma x y S,
      Gamma x = Some (TSchema S) ->
      Gamma y = Some (TPred S) ->
      Gamma |- t_filter x y \in TSchema S

  | T_ForEach : forall Gamma x y S S',
      Gamma x = Some(TSchema S) ->
      Gamma y = Some(TFn S S') ->
      Gamma |- t_foreach x y \in TSchema S'

  | T_LocalRearrange : forall Gamma x c S,
      Gamma x = Some (TSchema S) ->
      can_rearrange_by S c ->
      Gamma |- t_lrearrange x c \in (TSchema S)

  | T_GlobalRearrange : forall Gamma x c S,
      Gamma x = Some (TSchema S) ->
      can_rearrange_by S c ->
      Gamma |- t_grearrange x c \in (TSchema S)

  | T_Package : forall Gamma x c S,
      Gamma x = Some (TSchema S) ->
      can_package_by S c ->
      Gamma |- t_package x c \in TSchema (CTyNat *** (CTyBag S) ***)

  | T_Load : forall Gamma x T,
      Gamma x = None ->
      loadable_ty T ->
      Gamma |- t_load x T \in TUnit

  | T_Assign : forall Gamma x q S,
      Gamma x = None ->
      Gamma |- q \in TSchema S ->
      Gamma |- t_assign x q \in TUnit

  | T_Store : forall Gamma x S,
      Gamma x = Some (TSchema S) ->
      Gamma |- t_store x \in TUnit

  | T_SeqLoad : forall Gamma x T s1 s2,
      s1 = t_load x T ->
      Gamma |- s1 \in TUnit ->
      (extend Gamma x T) |- s2 \in TUnit ->
      Gamma |- t_seq s1 s2 \in TUnit

  | T_SeqAssign : forall Gamma x q s1 s2 S,
      s1 = t_assign x q ->
      Gamma |- q \in TSchema S ->
      Gamma |- s1 \in TUnit ->
      extend Gamma x (TSchema S) |- s2 \in TUnit ->
      Gamma |- t_seq s1 s2 \in TUnit

  | T_SeqStore : forall Gamma x s1 s2 S,
      s1 = t_store x ->
      Gamma x = Some (TSchema S) ->
      Gamma |- s1 \in TUnit ->
      Gamma |- s2 \in TUnit ->
      Gamma |- t_seq s1 s2 \in TUnit

  where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.


End Physical.
