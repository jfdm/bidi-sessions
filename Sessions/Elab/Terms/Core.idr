module Sessions.Elab.Terms.Core

import Sessions.Types.Local
import Sessions.Types.Local.Subset
import Sessions.Types.Local.Merge.Synthesis
import Sessions.AST

import Sessions.Elab.Expr
import Sessions.Elab.Local

%default total

mutual
  namespace Branches
    public export
    data Synth : (rs : SnocList Role)
              -> (fs : SnocList Fix)
              -> (ts : SnocList (String,Base))
              -> (tbs : List (String, Base))
              -> (tms : List (String, String, Synth.AST))
              -> (tys : List (Branch rs fs))
                     -> Type
      where
        End : Synth rs fs ts Nil Nil Nil
        Ext : Synth rs fs (ts :< (v, b)) tm ty
           -> Synth rs fs ts tbs tms tys
           -> Synth rs fs ts ((l,b)::tbs) ((l,v,tm)::tms) (B l b ty :: tys)

    export
    Uninhabited (Synth rs fs ts Nil (x::xs) urgh) where
      uninhabited End impossible
      uninhabited (Ext y z) impossible

    export
    Uninhabited (Synth rs fs ts (x::xs) Nil urgh) where
      uninhabited End impossible
      uninhabited (Ext y z) impossible

  namespace Cases
    public export
    data Synth : (rs : SnocList Role)
              -> (fs : SnocList Fix)
              -> (ts : SnocList (String,Base))
              -> (tbs : List (String, Base))
              -> (tms : List (String, String, Synth.AST))
              -> (tys : List (Local rs fs))
                     -> Type
      where
        End : Synth rs fs ts Nil Nil Nil
        Ext : Synth rs fs (ts :< (v, b)) tm ty
           -> Synth rs fs ts tbs tms tys
           -> Synth rs fs ts ((l,b)::tbs) ((l,v,tm)::tms) (ty :: tys)

    export
    Uninhabited (Cases.Synth rs fs ts Nil (x::xs) urgh) where
      uninhabited End impossible
      uninhabited (Ext y z) impossible

    export
    Uninhabited (Cases.Synth rs fs ts (x::xs) Nil urgh) where
      uninhabited End impossible
      uninhabited (Ext y z) impossible


  public export
  data Synth : (rs : SnocList Role)
            -> (fs : SnocList Fix)
            -> (ts : SnocList (String,Base))
            -> (tm : Synth.AST)
            -> (ty : Local rs fs)
                  -> Type
    where
      Stop : Synth rs fs ts Stop Stop
      Call : (n : Nat)
          -> (idx : AtIndex MkFix fs n)
                 -> Synth rs fs ts (Call n) (Call idx)

      Loop : (cont : Synth rs (fs :< (MkFix)) ts tm  ty)
                  -> Synth rs  fs    ts (Loop tm) (Rec ty)

      Send : {r : _}
          -> (prf  : AtIndex r rs n)
          -> (pe   : Expr ts v b)
          -> (cont : Synth rs fs ts tm ty)
                  -> Synth rs fs ts (Send n l v tm)
                                 (Comm SEND prf [B l b ty])

      Recv : {r : _}
          -> (idx : AtIndex r rs n)
          -> (bs  : Synth rs fs ts xs tms tys)
                 -> Synth rs fs ts (Recv n (SUM xs) tms) (Comm RECV idx tys)

      The : Local rs fs    tmty ty
         -> Check rs fs ts ty tm
         -> Synth rs fs ts (The tmty tm) ty

      If : {l,r : _}
        -> (cond : Expr ts BOOL c)
        -> (tt   : Synth rs fs ts ttm l)
        -> (ff   : Synth rs fs ts ffm r)
        -> (prf  : Merge l r ty)
                -> Synth rs fs ts (If c ttm ffm) ty

      Match : {xs,tys : _}
           -> (tm  : Synth.Expr ts m (SUM xs))
           -> (bs  : Cases.Synth rs fs ts xs tms tys)
           -> (prf : Merges Synthesis.Merge tys ty)
                  -> Synth rs fs ts (Match m tms) ty

  export
  Uninhabited (Synth rs fs ts (Recv n NAT s) ty) where
    uninhabited Stop impossible
    uninhabited (Call k idx) impossible
    uninhabited (Loop cont) impossible
    uninhabited (Send prf pe cont) impossible
    uninhabited (Recv idx bs) impossible
    uninhabited (The x y) impossible
    uninhabited (If cond tt ff prf) impossible
    uninhabited (Match tm bs prf) impossible

  export
  Uninhabited (Synth rs fs ts (Recv n BOOL s) ty) where
    uninhabited Stop impossible
    uninhabited (Call k idx) impossible
    uninhabited (Loop cont) impossible
    uninhabited (Send prf pe cont) impossible
    uninhabited (Recv idx bs) impossible
    uninhabited (The x y) impossible
    uninhabited (If cond tt ff prf) impossible
    uninhabited (Match tm bs prf) impossible

  public export
  data Check : (rs : SnocList Role)
            -> (fs : SnocList (Fix))
            -> (ts : SnocList (String,Base))
            -> (ty : Local rs fs)
            -> (tm : Check.AST)
                  -> Type
    where
      Switch : {tySyn : Local rs fs}
            -> Synth rs fs ts tm tySyn
            -> tySyn === tyCheck
            -> Check rs fs ts tyCheck (Switch tm)

-- [ EOF ]
