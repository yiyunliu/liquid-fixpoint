{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE FlexibleInstances     #-}
-- | This module contains the various instances for Subable,
--   which (should) depend on the visitors, and hence cannot
--   be in the same place as the @Term@ definitions.
module Language.Fixpoint.Types.Substitutions (
    mkSubst
  , isEmptySubst
  , substExcept
  , substfExcept
  , subst1Except
  , targetSubstSyms
  , filterSubst
  ) where

import           Data.Maybe
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S
import           Data.Semigroup            (Semigroup (..))
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Misc
import           Text.PrettyPrint.HughesPJ.Compat
import           Text.Printf               (printf)

instance (Eq s, Fixpoint s, Show s) => Semigroup (Subst s) where
  (<>) = catSubst

instance (Show s, Eq s, Fixpoint s) => Monoid (Subst s) where
  mempty  = emptySubst
  mappend = (<>)

filterSubst :: (FixSymbol -> Expr s -> Bool) -> Subst s -> Subst s
filterSubst f (Su m) = Su (M.filterWithKey f m)

emptySubst :: Subst s
emptySubst = Su M.empty

catSubst :: (Fixpoint s, Eq s, Show s) => Subst s -> Subst s -> Subst s
catSubst (Su s1) θ2@(Su s2) = Su $ M.union s1' s2
  where
    s1'                     = subst θ2 <$> s1

mkSubst :: [(FixSymbol, Expr s)] -> Subst s
mkSubst = Su . M.fromList . reverse . filter notTrivial
  where
    notTrivial (x, EVar (FS y)) = x /= y
    notTrivial _           = True

isEmptySubst :: Subst s -> Bool
isEmptySubst (Su xes) = M.null xes

targetSubstSyms :: forall s. (Show s, Fixpoint s, Eq s) => Subst s -> [FixSymbol]
targetSubstSyms (Su ms) = syms @[Expr s] @s $ M.elems ms


  
instance Subable () s where
  syms _      = []
  subst _ ()  = ()
  substf _ () = ()
  substa _ () = ()

instance (Subable a s, Subable b s) => Subable (a,b) s where
  syms  (x, y)   = syms @a @s x ++ syms @b @s y
  subst su (x,y) = (subst su x, subst su y)
  substf f (x,y) = (substf f x, substf f y)
  substa f (x,y) = (substa @a @s f x, substa @b @s f y)

instance Subable a s => Subable [a] s where
  syms   = concatMap (syms @a @s)
  subst  = fmap . subst
  substf = fmap . substf
  substa = fmap . substa @a @s

instance Subable a s => Subable (Maybe a) s where
  syms   = concatMap (syms @a @s) . maybeToList
  subst  = fmap . subst
  substf = fmap . substf
  substa = fmap . substa @a @s

 
instance Subable a s => Subable (M.HashMap k a) s where
  syms   = syms @[a] @s . M.elems
  subst  = M.map . subst
  substf = M.map . substf
  substa = M.map . substa @a @s

subst1Except :: (Eq s, Fixpoint s, Subable a s) => [FixSymbol] -> a -> (FixSymbol, Expr s) -> a
subst1Except xs z su@(x, _)
  | x `elem` xs = z
  | otherwise   = subst1 z su

substfExcept :: (FixSymbol -> Expr s) -> [FixSymbol] -> FixSymbol -> Expr s
substfExcept f xs y = if y `elem` xs then EVar (FS y) else f y

substExcept  :: Subst s -> [FixSymbol] -> Subst s
-- substExcept  (Su m) xs = Su (foldr M.delete m xs)
substExcept (Su xes) xs = Su $ M.filterWithKey (const . not . (`elem` xs)) xes

instance (Fixpoint s, Eq s) => Subable FixSymbol s where
  substa f                 = f
  substf f x               = subSymbol (Just (f x)) x
  subst su x               = subSymbol (Just $ appSubst su x) x -- subSymbol (M.lookup x s) x
  syms x                   = [x]

appSubst :: Subst s -> FixSymbol -> Expr s
appSubst (Su s) x = fromMaybe (EVar (FS x)) (M.lookup x s)

subSymbol :: (Fixpoint s, Eq s) => Maybe (Expr s) -> FixSymbol -> FixSymbol
subSymbol (Just (EVar (FS y))) _ = y
subSymbol Nothing         x = x
subSymbol a               b = errorstar (printf "Cannot substitute symbol %s with expression %s" (showFix b) (showFix a))

substfLam :: (Eq s, Fixpoint s, Show s) => (FixSymbol -> Expr s) -> (FixSymbol, Sort s) -> Expr s -> Expr s
substfLam f (x, st) e =  ELam (FS x, st) (substf (\y -> if y == x then EVar (FS x) else f y) e)

instance (Fixpoint s, Eq s, Show s) => Subable (Expr s) s where
  syms                     = exprSymbols
  substa f                 = substf @(Expr s) @s (EVar . FS . f)
  substf f (EApp s e)      = EApp (substf f s) (substf f e)
  substf f (ELam (FS x, st) e)      = substfLam f (x, st) e
  substf f (ECoerc a t e)  = ECoerc a t (substf f e)
  substf f (ENeg e)        = ENeg (substf f e)
  substf f (EBin op e1 e2) = EBin op (substf f e1) (substf f e2)
  substf f (EIte p e1 e2)  = EIte (substf f p) (substf f e1) (substf f e2)
  substf f (ECst e so)     = ECst (substf f e) so
  substf f (EVar (FS x))   = f x
  substf f (PAnd ps)       = PAnd $ map (substf f) ps
  substf f (POr  ps)       = POr  $ map (substf f) ps
  substf f (PNot p)        = PNot $ substf f p
  substf f (PImp p1 p2)    = PImp (substf f p1) (substf f p2)
  substf f (PIff p1 p2)    = PIff (substf f p1) (substf f p2)
  substf f (PAtom r e1 e2) = PAtom r (substf f e1) (substf f e2)
  substf _ p@(PKVar _ _)   = p
  substf _  (PAll _ _)     = errorstar "substf: FORALL"
  substf f (PGrad k su i e)= PGrad k su i (substf f e)
  substf _  p              = p


  subst su (EApp f e)      = EApp (subst su f) (subst su e)
  subst su (ELam x@(FS x', _) e)      = ELam x (subst (removeSubst su x') e)
  subst su (ECoerc a t e)  = ECoerc a t (subst su e)
  subst su (ENeg e)        = ENeg (subst su e)
  subst su (EBin op e1 e2) = EBin op (subst su e1) (subst su e2)
  subst su (EIte p e1 e2)  = EIte (subst su p) (subst su e1) (subst su e2)
  subst su (ECst e so)     = ECst (subst su e) so
  subst su (EVar (FS x))   = appSubst su x
  subst su (PAnd ps)       = PAnd $ map (subst su) ps
  subst su (POr  ps)       = POr  $ map (subst su) ps
  subst su (PNot p)        = PNot $ subst su p
  subst su (PImp p1 p2)    = PImp (subst su p1) (subst su p2)
  subst su (PIff p1 p2)    = PIff (subst su p1) (subst su p2)
  subst su (PAtom r e1 e2) = PAtom r (subst su e1) (subst su e2)
  subst su (PKVar k su')   = PKVar k $ su' `catSubst` su
  subst su (PGrad k su' i e) = PGrad k (su' `catSubst` su) i (subst su e)
  subst su (PAll bs p)
          | disjoint su bs = PAll bs $ subst su p --(substExcept su (fst <$> bs)) p
          | otherwise      = errorstar "subst: PAll (without disjoint binds)"
  subst su (PExist bs p)
          | disjoint su bs = PExist bs $ subst su p --(substExcept su (fst <$> bs)) p
          | otherwise      = errorstar ("subst: EXISTS (without disjoint binds)" ++ show (bs, su, p))
  subst _  p               = p

removeSubst :: Subst s -> FixSymbol -> Subst s
removeSubst (Su su) x = Su $ M.delete x su

disjoint :: forall s. (Show s, Fixpoint s, Eq s) => Subst s -> [(FixSymbol, Sort s)] -> Bool
disjoint (Su su) bs = S.null $ suSyms `S.intersection` bsSyms
  where
    suSyms = S.fromList $ syms @[Expr s] @s (M.elems su) ++ syms @_ @s (M.keys su)
    bsSyms = S.fromList $ syms @_ @s $ fst <$> bs

instance (Eq s, Fixpoint s) => Semigroup (Expr s) where
  p <> q = pAnd [p, q]

instance (Eq s, Fixpoint s) => Monoid (Expr s) where
  mempty  = PTrue
  mappend = (<>)
  mconcat = pAnd

instance (Eq s, Fixpoint s, Show s) => Semigroup (Reft s) where
  (<>) = meetReft

instance (Eq s, Fixpoint s, Show s) => Monoid (Reft s) where
  mempty  = trueReft
  mappend = (<>)

meetReft :: forall s. (Eq s, Fixpoint s, Show s) => Reft s -> Reft s -> Reft s
meetReft (Reft (v, ra)) (Reft (v', ra'))
  | v == v'          = Reft (v , ra  `mappend` ra')
  | v == dummySymbol = Reft (v', ra' `mappend` (subst1 @_ @s ra (v , EVar (FS v'))))
  | otherwise        = Reft (v , ra  `mappend` (subst1 @_ @s ra' (v', EVar (FS v) )))

instance (Show s, Eq s, Fixpoint s) => Semigroup (SortedReft s) where
  t1 <> t2 = RR (mappend (sr_sort t1) (sr_sort t2)) (mappend (sr_reft t1) (sr_reft t2))

instance (Show s, Eq s, Fixpoint s) => Monoid (SortedReft s) where
  mempty  = RR mempty mempty
  mappend = (<>)

instance (Fixpoint s, Eq s, Show s) => Subable (Reft s) s where
  syms (Reft (v, ras))      = v : syms @_ @s ras
  substa f (Reft (v, ras))  = Reft (f v, substa @_ @s f ras)
  subst su (Reft (v, ras))  = Reft (v, subst (substExcept su [v]) ras)
  substf f (Reft (v, ras))  = Reft (v, substf (substfExcept f [v]) ras)
  subst1 (Reft (v, ras)) su = Reft (v, subst1Except [v] ras su)

instance (Fixpoint s, Eq s, Show s) => Subable (SortedReft s) s where
  syms               = syms @_ @s . sr_reft
  subst su (RR so r) = RR so $ subst su r
  substf f (RR so r) = RR so $ substf f r
  substa f (RR so r) = RR so $ substa @_ @s f r

instance (Eq s, Fixpoint s, Show s) => Reftable () s where
  isTauto _ = True
  ppTy _  d = d
  top  _    = ()
  bot  _    = ()
  meet _ _  = ()
  toReft _  = mempty
  ofReft _  = mempty
  params _  = []

instance (Show s, Fixpoint s, Eq s) => Reftable (Reft s) s where
  isTauto  = all isTautoPred . conjuncts . reftPred
  ppTy     = pprReft
  toReft   = id
  ofReft   = id
  params _ = []
  bot    _        = falseReft
  top (Reft(v,_)) = Reft (v, mempty)

pprReft :: (Eq s, Fixpoint s) => Reft s -> Doc -> Doc
pprReft (Reft (v, p)) d
  | isTautoPred p
  = d
  | otherwise
  = braces (toFix v <+> colon <+> d <+> text "|" <+> ppRas [p])

instance (Fixpoint s, Show s, Eq s) => Reftable (SortedReft s) s where
  isTauto  = isTauto @_ @s . toReft @_ @s
  ppTy     = ppTy @_ @s . toReft @_ @s
  toReft   = sr_reft
  ofReft   = errorstar "No instance of ofReft for SortedReft"
  params _ = []
  bot s    = s { sr_reft = falseReft }
  top s    = s { sr_reft = trueReft }

-- RJ: this depends on `isTauto` hence, here.
instance (Eq s, Show s, Fixpoint s, PPrint s) => PPrint (Reft s) where
  pprintTidy k r
    | isTauto @_ @s r  = text "true"
    | otherwise        = pprintReft k r

instance (Eq s, Fixpoint s, PPrint s) => PPrint (SortedReft s) where
  pprintTidy k (RR so (Reft (v, ras)))
    = braces
    $ pprintTidy k v <+> text ":" <+> toFix so <+> text "|" <+> pprintTidy k ras

instance (Eq s, Fixpoint s) => Fixpoint (Reft s) where
  toFix = pprReftPred

instance (Eq s, Fixpoint s) => Fixpoint (SortedReft s) where
  toFix (RR so (Reft (v, ra)))
    = braces
    $ toFix v <+> text ":" <+> toFix so <+> text "|" <+> toFix (conjuncts ra)

instance (Eq s, Fixpoint s) => Show (Reft s) where
  show = showFix

instance (Eq s, Fixpoint s) => Show (SortedReft s) where
  show  = showFix

pprReftPred :: (Eq s, Fixpoint s) => Reft s -> Doc
pprReftPred (Reft (_, p))
  | isTautoPred p
  = text "true"
  | otherwise
  = ppRas [p]

ppRas :: (Fixpoint s, Eq s) => [Expr s] -> Doc
ppRas = cat . punctuate comma . map toFix . flattenRefas

--------------------------------------------------------------------------------
-- | TODO: Rewrite using visitor -----------------------------------------------
--------------------------------------------------------------------------------
-- exprSymbols :: Expr s -> [FixSymbol]
-- exprSymbols = go
  -- where
    -- go (EVar x)           = [x]
    -- go (EApp f e)         = go f ++ go e
    -- go (ELam (x,_) e)     = filter (/= x) (go e)
    -- go (ECoerc _ _ e)     = go e
    -- go (ENeg e)           = go e
    -- go (EBin _ e1 e2)     = go e1 ++ go e2
    -- go (EIte p e1 e2)     = exprSymbols p ++ go e1 ++ go e2
    -- go (ECst e _)         = go e
    -- go (PAnd ps)          = concatMap go ps
    -- go (POr ps)           = concatMap go ps
    -- go (PNot p)           = go p
    -- go (PIff p1 p2)       = go p1 ++ go p2
    -- go (PImp p1 p2)       = go p1 ++ go p2
    -- go (PAtom _ e1 e2)    = exprSymbols e1 ++ exprSymbols e2
    -- go (PKVar _ (Su su))  = syms (M.elems su)
    -- go (PAll xts p)       = (fst <$> xts) ++ go p
    -- go _                  = []

exprSymbols :: forall s. (Fixpoint s, Eq s, Show s) => Expr s -> [FixSymbol]
exprSymbols = S.toList . go
  where
    gos es                = S.unions (go <$> es)
    go :: Expr s -> S.HashSet FixSymbol
    go (EVar (FS x))      = S.singleton x
    go (EApp f e)         = gos [f, e] 
    go (ELam ((FS x),_) e)= S.delete x (go e)
    go (ELam ((AS _),_) _)= error "GHC Symbol should be extracted as well"
    go (ECoerc _ _ e)     = go e
    go (ENeg e)           = go e
    go (EBin _ e1 e2)     = gos [e1, e2] 
    go (EIte p e1 e2)     = gos [p, e1, e2] 
    go (ECst e _)         = go e
    go (PAnd ps)          = gos ps
    go (POr ps)           = gos ps
    go (PNot p)           = go p
    go (PIff p1 p2)       = gos [p1, p2] 
    go (PImp p1 p2)       = gos [p1, p2]
    go (PAtom _ e1 e2)    = gos [e1, e2] 
    go (PKVar _ (Su su))  = S.fromList $ syms @_ @s $ M.elems su
    go (PAll xts p)       = go p `S.difference` S.fromList (fst <$> xts) 
    go (PExist xts p)     = go p `S.difference` S.fromList (fst <$> xts) 
    go _                  = S.empty 

