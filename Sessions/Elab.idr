module Sessions.Elab

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
      Call : (idx : AtIndex (MkFix f) fs n)
                 -> Synth rs fs ts (Call f) (Call idx)
      Loop : (cont : Synth rs (fs :< (MkFix f)) ts tm  ty)
                  -> Synth rs  fs    ts (Loop f  tm) (Rec f ty)

      Send : (prf  : Elem (MkRole r) rs)
          -> (cont : Synth rs fs ts tm ty)
                  -> Synth rs fs ts (Send r l b tm)
                                 (Comm SEND idx [B l b ty])

      Recv : (idx : Elem (MkRole r) rs)
          -> (bs  : Synth rs fs ts tms tys)
                 -> Synth rs fs ts (Recv r tms) (Comm RECV idx tys)

      If : (l,r : Local rs fs)
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
      Switch : (tySyn : Local rs fs)
            -> Synth rs fs ts tm tySyn
            -> Subset tySyn tyCheck
            -> Check rs fs ts tyCheck (Switch tm)

namespace Check
  export
  unique : Check rs fs ts a tm
        -> Check rs fs ts b tm
        -> a === b

namespace Branches
  export
  synth : (rs : SnocList Role)
       -> (fs : SnocList (Fix))
       -> (ts : SnocList (String,Base))
       -> (tms : List (String, String, Base, Synth.AST))
              -> Dec (DPair (List (Branch rs fs))
                            (Synth rs fs ts tms))

export
synth : (rs : SnocList Role)
     -> (fs : SnocList (Fix))
     -> (ts : SnocList (String,Base))
     -> (tm : Synth.AST)
           -> Dec (DPair (Local rs fs)
                         (Synth rs fs ts tm))

export
check : (rs : SnocList Role)
     -> (fs : SnocList (Fix))
     -> (ts : SnocList (String,Base))
     -> (ty : Local rs fs)
     -> (tm : Check.AST)
           -> Dec (Check rs fs ts ty tm)


namespace Branches
  synth rs fs ts []
    = Yes ([] ** End)
  synth rs fs ts ((l,v,b,k) :: xs) with (synth rs fs (ts :< (v,b)) k)
    synth rs fs ts ((l,v,b,k) :: xs) | (Yes (ty ** tm)) with (synth rs fs ts xs)
      synth rs fs ts ((l,v,b,k) :: xs) | (Yes (ty ** tm)) | (Yes (tys ** tms))
        = Yes (B l b ty :: tys ** Ext tm tms)
      synth rs fs ts ((l,v,b,k) :: xs) | (Yes (ty ** tm)) | (No no)
        = No (\case ((B l b ty :: tys) ** (Ext x y)) => no (tys ** y))

    synth rs fs ts ((l,v,b,k) :: xs) | (No no)
      = No (\case ((B l b ty :: tys) ** (Ext x y)) => no (ty ** x))


checkFails : Local rs fs typetm type
          -> (Check rs fs ts type tm -> Void)
          -> DPair (Local rs fs)
                   (Synth rs fs ts (The typetm tm))
          -> Void
checkFails pl f (ty ** (The x y)) with (unique pl x)
  checkFails pl f (ty ** (The x y)) | Refl = f y

synth rs fs ts Stop
  = Yes (Stop ** Stop)

synth rs fs ts (Call str) with (AtIndex.lookup fs (MkFix str))
  synth rs fs ts (Call str) | (Yes (n ** prf))
    = Yes (Call prf ** Call prf)
  synth rs fs ts (Call str) | (No no)
    = No (\case ((Call idx) ** (Call idx)) => no (_ ** idx))

synth rs fs ts (Loop str k) with (synth rs (fs :< (MkFix str)) ts k)
  synth rs fs ts (Loop str k) | (Yes (ty ** prf))
    = Yes (Rec  str ty ** Loop prf)
  synth rs fs ts (Loop str k) | (No no)
    = No (\case ((Rec str ty) ** (Loop cont)) => no (ty ** cont))

synth rs fs ts (Send r l ty k) with (isElem (MkRole r) rs)
  synth rs fs ts (Send r l ty k) | (Yes ridx) with (synth rs fs ts k)
    synth rs fs ts (Send r l ty k) | (Yes ridx) | (Yes (lty ** prf))
      = Yes (Comm SEND ridx [B l ty lty] ** Send ridx prf)
    synth rs fs ts (Send r l ty k) | (Yes ridx) | (No no)
      = No (\case ((Comm SEND idx [B l _ ty]) ** (Send prf cont)) => no (ty ** cont))

  synth rs fs ts (Send r l ty k) | (No no)
    = No (\case ((Comm SEND idx [B l bty ty]) ** (Send prf cont)) => no prf)

synth rs fs ts (Recv r xs) with (isElem (MkRole r) rs)
  synth rs fs ts (Recv r xs) | (Yes ridx) with (synth rs fs ts xs)
    synth rs fs ts (Recv r xs) | (Yes ridx) | (Yes (fst ** snd))
      = Yes (Comm RECV _ fst ** Recv ridx snd)

    synth rs fs ts (Recv r xs) | (Yes ridx) | (No no)
      = No (\case ((Comm RECV idx tys) ** (Recv idx bs)) => no (tys ** bs))

  synth rs fs ts (Recv r xs) | (No no)
    = No (\case ((Comm RECV idx tys) ** (Recv idx bs)) => no idx)

synth rs fs ts (If c tt ff) with (check ts BOOL c)
  synth rs fs ts (If c tt ff) | (Yes cond) with (synth rs fs ts tt)
    synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) with (synth rs fs ts ff)
      synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) with (merge tyL tyR)
        synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) | (Yes (ty ** prf))
          = Yes (ty ** If tyL tyR cond pL pR prf)
        synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) | (No no)
          = No (\case (fst ** (If tyL tyR x y z prf)) => no (fst ** ?condMerge))
      synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (No no)
        = No (\case (fst ** (If _ _ _ y z _)) => no (_ ** z))
    synth rs fs ts (If c tt ff) | (Yes cond) | (No no)
      = No (\case (fst ** (If _ _ x_ y z _)) => no (_ ** y))

  synth rs fs ts (If c tt ff) | (No no)
    = No (\case (fst ** (If _ _ cond x y prf)) => no cond)

synth rs fs ts (The tytm tm) with (synth rs fs tytm)
  synth rs fs ts (The tytm tm) | (Yes (ty ** pTT)) with (check rs fs ts ty tm)
    synth rs fs ts (The tytm tm) | (Yes (ty ** pTT)) | (Yes tm')
      = Yes (ty ** The pTT tm')

    synth rs fs ts (The tytm tm) | (Yes (ty ** pTT)) | (No no)
      = No (checkFails pTT no)
      --(\case (ty ** (The ty x y)) => no ?theTyTy)

  synth rs fs ts (The tytm tm) | (No no)
    = No (\case (fst ** (The x y)) => no (fst ** x))

check rs fs ts ty (Switch tm) with (synth rs fs ts tm)
  check rs fs ts ty (Switch tm) | (Yes (tySyn ** prf)) with (subset tySyn ty)
    check rs fs ts ty (Switch tm) | (Yes (tySyn ** prf)) | (Yes prfS)
      = Yes (Switch tySyn prf prfS)
    check rs fs ts ty (Switch tm) | (Yes (tySyn ** prf)) | (No no)
      = No (\case (Switch ty x y) => no ?checkSynSubset)
  check rs fs ts ty (Switch tm) | (No no)
    = No (\case (Switch ty x y) => no (_ ** x))

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



-- [ EOF ]
