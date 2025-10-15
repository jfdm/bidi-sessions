module Sessions.Elab.Sessions

import public Sessions.Types.Common
import public Sessions.Types.Local
import        Sessions.Types.Local.Subset

import public Sessions.Types.Global
import public Sessions.Types.Global.Projection
import public Sessions.Types.Global.WellFormed

import Sessions.AST

import public Sessions.Elab.Expr
import public Sessions.Elab.Local
import public Sessions.Elab.Global
import public Sessions.Elab.Process

import Sessions.Terms.Sessions

%default total

public export
data SynAck : (rs : Role.Context)
           -> (tm : Session.AST)
           -> (l  : Local rs Lin)
                 -> Type
  where
    Session : {p : _}
           -> {tyProj,tySyn : Protocol LOCAL rs Lin}
           -> {tyG   : Protocol GLOBAL rs Lin}
           -> Global rs Lin tmty tyG
           -> WellFormed rs tyG
           -> (whom : AtIndex p rs n)
           -> Project whom tyG tyProj
           -> Synth rs Lin Lin tm tySyn
           -> Subset tySyn tyProj
           -> SynAck rs (Session tmty n tm) tySyn

projectFails : (widx : AtIndex w rs whom)
            -> Global rs Lin g gty
            -> (DPair (Local rs [<]) (Project widx gty) -> Void)
            -> (DPair (Local rs Lin) (SynAck rs (Session g whom tm))) -> Void
projectFails widx gty f (_ ** Session gtm wf whom p _ _) with (unique widx whom)
  projectFails widx gty f (_ ** Session gtm wf whom p _ _) | Refl with (unique2 widx whom)
    projectFails widx gty f (_ ** Session gtm wf widx p _ _) | Refl | Refl with (unique gty gtm)
      projectFails widx gty f (_ ** Session gtm wf widx p _ _) | Refl | Refl | Refl = f (_ ** p)

subsetFails : (Subset tySyn tyProj -> Void)
           -> (widx : AtIndex w rs whom )
           -> Project widx gty tyProj
           -> Global rs [<] g gty
           -> Synth rs [<] [<] tm tySyn
           -> (tySyn ** SynAck rs (Session g whom tm) tySyn) -> Void
subsetFails f pidx pGiv gGiv tmG (ty ** Session gExp wf y pExp tmExp prf) with (unique gGiv gExp)
  subsetFails f pidx pGiv gGiv tmG (ty ** Session gExp wf y pExp tmExp prf) | Refl with (unique tmG tmExp)
    subsetFails f pidx pGiv gGiv tmG (ty ** Session gExp wf y pExp tmExp prf) | Refl | Refl with (unique pidx y)
      subsetFails f pidx pGiv gGiv tmG (ty ** Session gExp wf y pExp tmExp prf) | Refl | Refl | Refl with (unique2 pidx y)
        subsetFails f pidx pGiv gGiv tmG (ty ** Session gExp wf pidx pExp tmExp prf) | Refl | Refl | Refl | Refl with (unique pGiv pExp)
          subsetFails f pidx pGiv gGiv tmG (ty ** Session gExp wf pidx pExp tmExp prf) | Refl | Refl | Refl | Refl | Refl = f prf

wellFormedFails : (WellFormed rs gty -> Void) -> Global rs [<] g gty -> (tySyn ** SynAck rs (Session g whom tm) tySyn) -> Void
wellFormedFails f ty (_ ** Session tye w _ _ _ _) with (unique ty tye)
  wellFormedFails f ty (_ ** Session tye w _ _ _ _) | Refl =  f w

export
check : (rs : SnocList Role)
     -> (tm : Session.AST)
           -> Dec (DPair (Local rs Lin) (SynAck rs tm))
check rs (Session g whom tm) with (synth rs Lin g)
  check rs (Session g whom tm) | (No no)
    = No $ \case (l ** Session gty _ _ _ _ _) => no (_ ** gty)

  check rs (Session g whom tm) | (Yes (gty ** gtm)) with (wellformed gty)
    check rs (Session g whom tm) | (Yes (gty ** gtm)) | (No no)
      = No (wellFormedFails no gtm)

    check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes pW) with (index rs whom)
      check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes pW) | (No no)
        = No $ \case (_ ** Session _ _ whom _ _ _) => no (_ ** whom)

      check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes pW) | (Yes (w ** widx)) with (project widx gty)
        check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes pW) | (Yes (w ** widx)) | (No no)
          = No (projectFails widx gtm no)

        check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes pW) | (Yes (w ** widx)) | (Yes (pty ** pP)) with (Process.synth rs Lin Lin tm)
          check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes pW) | (Yes (w ** widx)) | (Yes (pty ** pP)) | (No no)
            = No $ \case (_ ** Session _ _ _ _ pS _) => no (_ ** pS)

          check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes pW) | (Yes (w ** widx)) | (Yes (pty ** pP)) | (Yes (sty ** pS)) with (subset sty pty)
            check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes pW) | (Yes (w ** widx)) | (Yes (pty ** pP)) | (Yes (sty ** pS)) | (No no)
              = No (subsetFails no widx pP gtm pS)

            check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes pW) | (Yes (w ** widx)) | (Yes (pty ** pP)) | (Yes (sty ** pS)) | (Yes prf)
              = Yes (_ ** Session gtm pW widx pP pS prf)


namespace Convert

  export
  toTerm : SynAck rs tm local
        -> Session rs local
  toTerm (Session g pw whom _ p _)
    = MkSession (toTerm p)

-- [ EOF ]
