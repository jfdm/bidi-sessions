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
             -> (cmp : forall rs, fs . (a,b : Local rs fs) -> Type)
              -> (tms : List (String, String, Base, Synth.AST))
              -> (tys : List (Branch rs fs))
                     -> Type
      where
        End : {0 cmp : forall rs, fs . (a,b : Local rs fs) -> Type} -> Synth rs fs ts cmp Nil Nil
        Ext : {0 cmp : forall rs, fs . (a,b : Local rs fs) -> Type}
            -> Synth rs fs (ts :< (v, b)) cmp tm ty
           -> Synth rs fs ts cmp tms tys
           -> Synth rs fs ts cmp ((l,v,b,tm)::tms) (B l b ty :: tys)

  public export
  data Synth : (rs : SnocList Role)
            -> (fs : SnocList Fix)
            -> (ts : SnocList (String,Base))
            -> (cmp : forall rs, fs . (a,b : Local rs fs) -> Type)
            -> (tm : Synth.AST)
            -> (ty : Local rs fs)
                  -> Type
    where
      Stop : {0 cmp : forall rs, fs . (a,b : Local rs fs) -> Type}
          -> Synth rs fs ts cmp Stop Stop
      Call : {0 cmp : forall rs, fs . (a,b : Local rs fs) -> Type}
           -> (idx : AtIndex (MkFix f) fs n)
                 -> Synth rs fs ts cmp (Call f) (Call idx)
      Loop : {0 cmp : forall rs, fs . (a,b : Local rs fs) -> Type}
           -> (cont : Synth rs (fs :< (MkFix f)) ts cmp tm  ty)
                  -> Synth rs  fs    ts cmp (Loop f  tm) (Rec f ty)

      Send : {0 cmp : forall rs, fs . (a,b : Local rs fs) -> Type}
          -> (prf  : Elem (MkRole r) rs)
          -> (cont : Synth rs fs ts cmp tm ty)
                  -> Synth rs fs ts cmp (Send r l b tm)
                                 (Comm SEND idx [B l b ty])

      Recv : {0 cmp : forall rs, fs . (a,b : Local rs fs) -> Type}
          -> (idx : Elem (MkRole r) rs)
          -> (bs  : Synth rs fs ts cmp tms tys)
                 -> Synth rs fs ts cmp (Recv r tms) (Comm RECV idx tys)

      If : {0 cmp : forall rs, fs . (a,b : Local rs fs) -> Type}
        -> (l,r : Local rs fs)
        -> (cond : Expr ts BOOL c)
        -> (tt   : Synth rs fs ts cmp ttm l)
        -> (ff   : Synth rs fs ts cmp ffm r)
        -> (prf  : Merge l r ty)
                -> Synth rs fs ts cmp (If c ttm ffm) ty

      The : {0 cmp : forall rs, fs . (a,b : Local rs fs) -> Type}
         -> Local rs fs    tmty ty
         -> Check rs fs ts cmp ty tm
         -> Synth rs fs ts cmp (The tmty tm) ty

  public export
  data Check : (rs : SnocList Role)
            -> (fs : SnocList (Fix))
            -> (ts : SnocList (String,Base))
            -> (cmp : forall rs, fs . (a,b : Local rs fs) -> Type)
            -> (ty : Local rs fs)
            -> (tm : Check.AST)
                  -> Type
    where
      Switch : {0 cmp : forall rs, fs . (a,b : Local rs fs) -> Type}
            -> (tySyn : Local rs fs)
            -> Synth rs fs ts cmp tm tySyn
            -> cmp tySyn tyCheck
            -> Check rs fs ts cmp tyCheck (Switch tm)

namespace Check
  export
  unique : {0 cmp : forall rs, fs . (a,b : Local rs fs) -> Type}
        -> Check rs fs ts cmp a tm
        -> Check rs fs ts cmp b tm
        -> a === b

namespace Branches
  export
  synth : (rs : SnocList Role)
       -> (fs : SnocList (Fix))
       -> (ts : SnocList (String,Base))
       -> {0  cmp : forall rs, fs . (a,b : Local rs fs) -> Type }
       -> (f  : forall rs,fs . (a,b : Local rs fs) -> Dec (cmp a b))
       -> (tms : List (String, String, Base, Synth.AST))
              -> Dec (DPair (List (Branch rs fs))
                            (Synth rs fs ts cmp tms))

export
synth : (rs : SnocList Role)
     -> (fs : SnocList (Fix))
     -> (ts : SnocList (String,Base)) ->        {0  cmp : forall rs, fs . (a,b : Local rs fs) -> Type }
     -> (f  : forall rs,fs . (a,b : Local rs fs) -> Dec (cmp a b))
     -> (tm : Synth.AST)
           -> Dec (DPair (Local rs fs)
                         (Synth rs fs ts cmp tm))

export
check : (rs : SnocList Role)
     -> (fs : SnocList (Fix))
     -> (ts : SnocList (String,Base))       -> {0  cmp : forall rs , fs . (a,b : Local rs fs) -> Type }
     -> (f  : forall rs,fs . (a,b : Local rs fs) -> Dec (cmp a b))
     -> (ty : Local rs fs)
     -> (tm : Check.AST)
           -> Dec (Check rs fs ts cmp ty tm)


namespace Branches
  synth rs fs ts cmp []
    = Yes ([] ** End)
  synth rs fs ts cmp ((l,v,b,k) :: xs) with (synth rs fs (ts :< (v,b)) cmp k)
    synth rs fs ts cmp ((l,v,b,k) :: xs) | (Yes (ty ** tm)) with (synth rs fs ts cmp xs)
      synth rs fs ts cmp ((l,v,b,k) :: xs) | (Yes (ty ** tm)) | (Yes (tys ** tms))
        = Yes (B l b ty :: tys ** Ext tm tms)
      synth rs fs ts cmp ((l,v,b,k) :: xs) | (Yes (ty ** tm)) | (No no)
        = No (\case ((B l b ty :: tys) ** (Ext x y)) => no (tys ** y))

    synth rs fs ts cmp ((l,v,b,k) :: xs) | (No no)
      = No (\case ((B l b ty :: tys) ** (Ext x y)) => no (ty ** x))


--checkFails : Local rs fs typetm type
--          -> (Check cmp rs fs ts type tm -> Void)
--          -> DPair (Local rs fs)
--                   (Synth cmp rs fs ts (The typetm tm))
--          -> Void
--checkFails pl f (ty ** (The x y)) with (Local.unique pl x)
--  checkFails pl f (ty ** (The x y)) | Refl = f y

synth rs fs ts cmp Stop
  = Yes (Stop ** Stop)

synth rs fs ts cmp (Call str) with (AtIndex.lookup fs (MkFix str))
  synth rs fs ts cmp (Call str) | (Yes (n ** prf))
    = Yes (Call prf ** Call prf)
  synth rs fs ts cmp (Call str) | (No no)
    = No (\case ((Call idx) ** (Call idx)) => no (_ ** idx))

synth rs fs ts cmp (Loop str k) with (Elab.synth rs (fs :< (MkFix str)) ts cmp k)
  synth rs fs ts cmp (Loop str k) | (Yes (ty ** prf))
    = Yes (Rec  str ty ** Loop prf)
  synth rs fs ts cmp (Loop str k) | (No no)
    = No (\case ((Rec str ty) ** (Loop cont)) => no (ty ** cont))

synth rs fs ts cmp (Send r l ty k) with (isElem (MkRole r) rs)
  synth rs fs ts cmp (Send r l ty k) | (Yes ridx) with (synth rs fs ts cmp k)
    synth rs fs ts cmp (Send r l ty k) | (Yes ridx) | (Yes (lty ** prf))
      = Yes (Comm SEND ridx [B l ty lty] ** Send ridx prf)
    synth rs fs ts cmp (Send r l ty k) | (Yes ridx) | (No no)
      = No (\case ((Comm SEND idx [B l _ ty]) ** (Send prf cont)) => no (ty ** cont))

  synth rs fs ts cmp (Send r l ty k) | (No no)
    = No (\case ((Comm SEND idx [B l bty ty]) ** (Send prf cont)) => no prf)

synth rs fs ts cmp (Recv r xs) with (isElem (MkRole r) rs)
  synth rs fs ts cmp (Recv r xs) | (Yes ridx) with (synth rs fs ts cmp xs)
    synth rs fs ts cmp (Recv r xs) | (Yes ridx) | (Yes (fst ** snd))
      = Yes (Comm RECV _ fst ** Recv ridx snd)

    synth rs fs ts cmp (Recv r xs) | (Yes ridx) | (No no)
      = No (\case ((Comm RECV idx tys) ** (Recv idx bs)) => no (tys ** bs))

  synth rs fs ts cmp (Recv r xs) | (No no)
    = No (\case ((Comm RECV idx tys) ** (Recv idx bs)) => no idx)

synth rs fs ts cmp (If c tt ff) with (check ts BOOL c)
  synth rs fs ts cmp (If c tt ff) | (Yes cond) with (synth rs fs ts cmp tt)
    synth rs fs ts cmp (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) with (synth rs fs ts cmp ff)
      synth rs fs ts cmp (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) with (merge tyL tyR)
        synth rs fs ts cmp (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) | (Yes (ty ** prf))
          = Yes (ty ** If tyL tyR cond pL pR prf)
        synth rs fs ts cmp (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) | (No no)
          = No (\case (fst ** (If tyL tyR x y z prf)) => no (fst ** ?condMerge))
      synth rs fs ts cmp (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (No no)
        = No (\case (fst ** (If _ _ _ y z _)) => no (_ ** z))
    synth rs fs ts cmp (If c tt ff) | (Yes cond) | (No no)
      = No (\case (fst ** (If _ _ x_ y z _)) => no (_ ** y))

  synth rs fs ts cmp (If c tt ff) | (No no)
    = No (\case (fst ** (If _ _ cond x y prf)) => no cond)

synth rs fs ts cmp (The tytm tm) with (synth rs fs tytm)
  synth rs fs ts cmp (The tytm tm) | (Yes (ty ** pTT)) with (check rs fs ts cmp ty tm)
    synth rs fs ts cmp (The tytm tm) | (Yes (ty ** pTT)) | (Yes tm')
      = Yes (ty ** The pTT tm')

    synth rs fs ts cmp (The tytm tm) | (Yes (ty ** pTT)) | (No no)
      = No ?checkFails
      -- (checkFails pTT no)
      --(\case (ty ** (The ty x y)) => no ?theTyTy)

  synth rs fs ts cmp (The tytm tm) | (No no)
    = No (\case (fst ** (The x y)) => no (fst ** x))

check rs fs ts cmp ty (Switch tm) with (synth rs fs ts cmp tm)
  check rs fs ts cmp ty (Switch tm) | (Yes (tySyn ** prf)) with (cmp tySyn ty)
    check rs fs ts cmp ty (Switch tm) | (Yes (tySyn ** prf)) | (Yes prfS)
      = Yes (Switch tySyn prf prfS)
    check rs fs ts cmp ty (Switch tm) | (Yes (tySyn ** prf)) | (No no)
      = No (\case (Switch ty x y) => no y)
  check rs fs ts cmp ty (Switch tm) | (No no)
    = No (\case (Switch ty x y) => no (_ ** x))

namespace Session
  public export
  data Check : (rs : SnocList Role)
            -> (ts : SnocList (String,Base))
            -> (tm : Session.AST)
                  -> Type
    where
      Session : Local rs Lin tmty tyExp
             -> Synth rs Lin ts Subset tm tySyn
             -> Subset tySyn tyExp
             -> Check rs ts (Session tmty tm)
             -- here we can do projection...



-- [ EOF ]
