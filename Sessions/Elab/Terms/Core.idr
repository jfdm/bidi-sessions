module Sessions.Elab.Terms.Core

import Sessions.Types.Local
import Sessions.Types.Local.Subset
import Sessions.Types.Local.Merge.Synthesis
import Sessions.AST

import Sessions.Elab.Expr
import Sessions.Elab.Local

mutual
  namespace Branches
    public export
    data Synth : (rs : SnocList Role)
              -> (fs : SnocList Fix)
              -> (ts : SnocList (String,Base))
              -> (tms : List (String, String, Base, Synth.AST))
              -> (tys : List (Branch rs fs))
                     -> Type
      where
        End : Synth rs fs ts Nil Nil
        Ext : Synth rs fs (ts :< (v, b)) tm ty
           -> Synth rs fs ts tms tys
           -> Synth rs fs ts ((l,v,b,tm)::tms) (B l b ty :: tys)

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
          -> (cont : Synth rs fs ts tm ty)
                  -> Synth rs fs ts (Send n l b tm)
                                 (Comm SEND prf [B l b ty])

      Recv : {r : _}
          -> (idx : AtIndex r rs n)
          -> (bs  : Synth rs fs ts tms tys)
                 -> Synth rs fs ts (Recv n tms) (Comm RECV idx tys)

      If : {l,r : _}
        -> (cond : Expr ts BOOL c)
        -> (tt   : Synth rs fs ts ttm l)
        -> (ff   : Synth rs fs ts ffm r)
        -> (prf  : Merge l r ty)
                -> Synth rs fs ts (If c ttm ffm) ty

      The : Local rs fs    tmty ty
         -> Check rs fs ts ty tm
         -> Synth rs fs ts (The tmty tm) ty

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
            -> Subset tySyn tyCheck
            -> Check rs fs ts tyCheck (Switch tm)

-- [ EOF ]
