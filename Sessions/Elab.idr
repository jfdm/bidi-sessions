module Sessions.Elab

import Sessions.Types.Local
import Sessions.Types.Local.Subset
import Sessions.Types.Local.Merge
import Sessions.AST

namespace Synth
  namespace Exprs

    public export
    data Expr : SnocList (String,Base) -> Synth.Expr -> Base -> Type where
      True : Expr ts True BOOL
      False : Expr ts False BOOL
      N : Expr ts (N n) NAT
      V : Elem (v,b) ts
       -> Expr ts (V v) b


    unbound : ((v : Base ** Elem (str, v) ts) -> Void) -> DPair Base (Expr ts (V str)) -> Void
    unbound f (fst ** (V x)) = f (fst ** x)

    export
    synth : (ts  : SnocList (String,Base))
         -> (ast : Synth.Expr)
                -> Dec (DPair Base (Expr ts ast))
    synth ts True = Yes (BOOL ** True)
    synth ts False = Yes (BOOL ** False)
    synth ts (N k) = Yes (NAT ** N)
    synth ts (V str) with (lookup str ts)
      synth ts (V str) | (Yes (ty ** idx)) = Yes (ty ** V idx)
      synth ts (V str) | (No no)
        = No (unbound no)

namespace Synth
  namespace Local
    namespace Branches
      public export
      data Local : (how : (rs : SnocList Role)
                       -> (fs : SnocList Fix)
                       -> (tm : Local)
                       -> (ty : Local rs fs)
                             -> Type)
                -> (rs  : SnocList Role)
                -> (fs  : SnocList Fix)
                -> (tms : List (String, Base, Local))
                -> (tys : List (Branch rs fs))
                       -> Type
        where
          End : Local how rs fs Nil Nil
          Ext : {0 how : (rs : SnocList Role)
                      -> (fs : SnocList Fix)
                      -> (tm : Local)
                      -> (ty : Local rs fs)
                            -> Type}
             -> (head : how rs fs ktm kty)
             -> (next : Local how rs fs tms tys)
                     -> Local how rs fs ((l,b,ktm)::tms) (B l b kty :: tys)

      export
      synth : {0 how : (rs : SnocList Role)
                    -> (fs : SnocList Fix)
                    -> (tm : Local)
                    -> (ty : Local rs fs)
                          -> Type}
           -> (f : (rs : SnocList Role)
                -> (fs : SnocList Fix)
                -> (tm : Local)
                      -> Dec (DPair (Local rs fs) (how rs fs tm)))
           -> (rs  : SnocList Role)
           -> (fs  : SnocList Fix)
           -> (tms : List (String, Base, Local))
                  -> Dec (DPair (List (Branch rs fs))
                                (Branches.Local how rs fs tms))
      synth f rs fs []
        = Yes ([] ** End)

      synth f rs fs ((l,b,x) :: xs) with (f rs fs x)
        synth f rs fs ((l,b,x) :: xs) | (Yes (ty ** tm)) with (synth f rs fs xs)
          synth f rs fs ((l,b,x) :: xs) | (Yes (ty ** tm)) | (Yes (tys ** tms))
            = Yes (B l b ty :: tys ** Ext tm tms)
          synth f rs fs ((l,b,x) :: xs) | (Yes (ty ** tm)) | (No no)
            = No (\case ((B l b kty :: tys) ** (Ext head next)) => no (tys ** next))

        synth f rs fs ((l,b,x) :: xs) | (No noH)
          = No (\case ((B l b kty :: tys) ** (Ext head next)) => noH (kty ** head))

    public export
    data Local : (rs : SnocList Role)
              -> (fs : SnocList Fix)
              -> (tm : Local)
              -> (ty : Local rs fs)
                    -> Type
      where
        End : Local rs fs End Stop
        Call : (idx : Elem (MkFix f) fs)
                   -> Local rs fs (Call f) (Call idx)
        Rec : Local rs (fs :< MkFix f) kast kty
           -> Local rs fs (Rec f kast) (Rec (MkFix f) kty)

        Comm : (idx : Elem (MkRole r) rs)
            -> Local Local rs fs tms tys
            -> Local rs fs (Comm cty r tms) (Comm cty idx tys)

    export
    synth : (rs : SnocList Role)
         -> (fs : SnocList Fix)
         -> (tm : Local)
               -> Dec (DPair (Local rs fs)
                             (Local rs fs tm))
    synth rs fs End
      = Yes (Stop ** End)

    synth rs fs (Call str) with (isElem (MkFix str) fs)
      synth rs fs (Call str) | (Yes prf)
        = Yes (Call prf ** Call prf)
      synth rs fs (Call str) | (No no)
        = No (\case ((Call idx) ** (Call idx)) => no idx)

    synth rs fs (Rec str k) with (synth rs (fs :< MkFix str) k)
      synth rs fs (Rec str k) | (Yes (kty ** prf))
        = Yes (Rec (MkFix str) kty ** Rec prf)
      synth rs fs (Rec str k) | (No no)
        = No (\case ((Rec (MkFix str) kty) ** (Rec x)) => no (kty ** x))

    synth rs fs (Comm cty r bs) with (isElem (MkRole r) rs)
      synth rs fs (Comm cty r bs) | (Yes ridx) with (synth synth rs fs bs)
        synth rs fs (Comm cty r bs) | (Yes ridx) | (Yes (tys ** tms))
          = Yes (Comm cty ridx tys ** Comm ridx tms)
        synth rs fs (Comm cty r bs) | (Yes ridx) | (No no)
          = No (\case ((Comm cty idx tys) ** (Comm idx x)) => no (tys ** x))

      synth rs fs (Comm cty r bs) | (No no)
        = No (\case (Comm cty idx tys ** Comm idx x) => no idx)


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
      Call : (idx : Elem (MkFix f) fs)
                 -> Synth rs fs ts (Call f) (Call idx)
      Loop : (cont : Synth rs (fs :< MkFix f) ts tm  ty)
                  -> Synth rs  fs    ts (Loop f  tm) (Rec (MkFix f) ty)

      Send : (prf  : Elem (MkRole r) rs)
          -> (cont : Synth rs fs ts tm ty)
                  -> Synth rs fs ts (Send r l b tm)
                                 (Comm SEND idx [B l b ty])

      Recv : (idx : Elem (MkRole r) rs)
          -> (bs  : Synth rs fs ts tms tys)
                 -> Synth rs fs ts (Recv r tms) (Comm RECV idx tys)

      The : Local rs fs    tmty ty
         -> Check rs fs ts ty (Switch tm)
         -> Synth rs fs ts (The tmty tm) ty

  public export
  data Check : (rs : SnocList Role)
            -> (fs : SnocList Fix)
            -> (ts : SnocList (String,Base))
            -> (ty : Local rs fs)
            -> (tm : Check.AST)
                  -> Type
    where
      Switch : Synth rs fs ts tm tySyn
            -> Subset tySyn tyCheck
            -> Check rs fs ts tyCheck (Switch tm)

  namespace Session
    public export
    data Check : (rs : SnocList Role)
              -> (ts : SnocList (String,Base))
              -> (tm : Session.AST)
                    -> Type
      where
        Session : Local rs Lin tmty tyExp
               -> Synth rs Lin ts tm tySyn
               -> Subset tySyn tyExp
               -> Check rs ts (Session tmty tm)
               -- here we can do projection...
{-mutual
  namespace Synth

    public export
    data AST = Stop
             | Call String
             | Loop String Synth.AST
             | Send String Base String Synth.AST
             | Recv String (List (String, Base, Synth.AST))
             | If Expr Synth.AST Synth.AST
             | The Local Synth.AST

  namespace Check

    public export
    data AST = Session Local Synth.AST
             | Switch Synth.AST
-}
