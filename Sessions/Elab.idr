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
