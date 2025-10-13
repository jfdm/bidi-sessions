module Sessions.Terms.Process

import Sessions.Types.Local
import Sessions.Types.Local.Subset
import Sessions.Types.Local.Merge.Synthesis
import Sessions.AST

import Sessions.Terms.Expr

%default total

mutual

  namespace Branches
    public export
    data Branches : (rs : SnocList Role)
                 -> (fs : SnocList Fix)
                 -> (ts : SnocList (Base))
                 -> (tbs : List (String, Base))
                 -> (tys : List (Branch rs fs))
                        -> Type
      where
        End : Branches rs fs ts Nil Nil
        Ext : Process rs fs (ts :< b) ty
           -> Branches rs fs ts tbs tys
           -> Branches rs fs ts ((l,b)::tbs) (B l b ty :: tys)

  namespace Cases
    public export
    data Cases : (rs : SnocList Role)
              -> (fs : SnocList Fix)
              -> (ts : SnocList (Base))
              -> (tbs : List (String, Base))
              -> (tys : List (Local rs fs))
                     -> Type
      where
        End : Cases rs fs ts Nil Nil
        Ext : Process rs fs (ts :< b) ty
           -> Cases rs fs ts tbs tys
           -> Cases rs fs ts ((l,b)::tbs) (ty :: tys)

  public export
  data Process : (rs : SnocList Role)
              -> (fs : SnocList Fix)
              -> (ts : SnocList (Base))
              -> (ty : Local rs fs)
                    -> Type
    where
      Stop : Process rs fs ts Stop
      Call : (idx : AtIndex MkFix fs n)
                 -> Process rs fs ts (Call idx)
      Loop : (cont : Process rs (fs :< MkFix) ts ty)
                  -> Process rs fs ts (Rec idx)

      Send : {r : _}
          -> (prf  : AtIndex r rs n)
          -> (pe   : Expr ts b)
          -> (cont : Process rs fs ts ty)
                  -> Process rs fs ts (Comm SEND prf [B l b ty])

      Recv : {r : _}
          -> (idx : AtIndex r rs n)
          -> (bs  : Branches rs fs ts xs tys)
                 -> Process  rs fs ts (Comm RECV idx tys)

      If : {l,r : _}
        -> (cond : Expr ts BOOL)
        -> (tt   : Process rs fs ts l)
        -> (ff   : Process rs fs ts r)
        -> (prf  : Merge l r ty)
                -> Process rs fs ts ty

      Match : {xs,tys : _}
           -> (m   : Expr ts (SUM xs))
           -> (bs  : Cases rs fs ts xs tys)
           -> (prf : Merges Synthesis.Merge tys ty)
                  -> Process rs fs ts ty
