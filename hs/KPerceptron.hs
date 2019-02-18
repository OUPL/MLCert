{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module KPerceptron where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

data Unit =
   Tt

data Nat =
   O
 | S Nat

data Option a =
   Some a
 | None

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
sub :: Nat -> Nat -> Nat
sub n m =
  case n of {
   O -> n;
   S k -> case m of {
           O -> n;
           S l -> sub k l}}

eqb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
eqb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False ->
    case b2 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

data Reflect =
   ReflectT
 | ReflectF

apply :: (a1 -> a2) -> a2 -> (Option a1) -> a2
apply f x u =
  case u of {
   Some y -> f y;
   None -> x}

bind :: (a1 -> Option a2) -> (Option a1) -> Option a2
bind f =
  apply f None

data Simpl_fun aT rT =
   SimplFun (aT -> rT)

fun_of_simpl :: (Simpl_fun a1 a2) -> a1 -> a2
fun_of_simpl f x =
  case f of {
   SimplFun lam -> lam x}

funcomp :: Unit -> (a2 -> a1) -> (a3 -> a2) -> a3 -> a1
funcomp _ f g x =
  f (g x)

pcomp :: (a2 -> Option a1) -> (a3 -> Option a2) -> a3 -> Option a1
pcomp f g x =
  bind f (g x)

iffP :: Prelude.Bool -> Reflect -> Reflect
iffP _ pb =
  let {_evar_0_ = \_ _ _ -> ReflectT} in
  let {_evar_0_0 = \_ _ _ -> ReflectF} in
  case pb of {
   ReflectT -> _evar_0_ __ __ __;
   ReflectF -> _evar_0_0 __ __ __}

idP :: Prelude.Bool -> Reflect
idP b1 =
  case b1 of {
   Prelude.True -> ReflectT;
   Prelude.False -> ReflectF}

type Pred t = t -> Prelude.Bool

type Rel t = t -> Pred t

type Simpl_pred t = Simpl_fun t Prelude.Bool

simplPred :: (Pred a1) -> Simpl_pred a1
simplPred p =
  SimplFun p

pred_of_simpl :: (Simpl_pred a1) -> Pred a1
pred_of_simpl =
  fun_of_simpl

predT :: Simpl_pred a1
predT =
  simplPred (\_ -> Prelude.True)

data Mem_pred t =
   Mem (Pred t)

data PredType0 t =
   PredType (Any -> Pred t) (Any -> Mem_pred t)

type Pred_sort t = Any

predPredType :: PredType0 a1
predPredType =
  PredType (\x -> unsafeCoerce x) (\p -> Mem (\x -> unsafeCoerce p x))

pred_of_mem :: (Mem_pred a1) -> Pred_sort a1
pred_of_mem mp =
  case mp of {
   Mem p -> unsafeCoerce p}

sort_of_simpl_pred :: (Simpl_pred a1) -> Pred_sort a1
sort_of_simpl_pred p =
  unsafeCoerce pred_of_simpl p

pred_of_argType :: Simpl_pred a1
pred_of_argType =
  predT

mem :: (PredType0 a1) -> (Pred_sort a1) -> Mem_pred a1
mem pT =
  case pT of {
   PredType _ s -> s}

in_mem :: a1 -> (Mem_pred a1) -> Prelude.Bool
in_mem x mp =
  unsafeCoerce pred_of_mem mp x

pred_of_mem_pred :: (Mem_pred a1) -> Simpl_pred a1
pred_of_mem_pred mp =
  simplPred (\x -> in_mem x mp)

type Axiom t = t -> t -> Reflect

data Mixin_of t =
   Mixin (Rel t) (Axiom t)

op :: (Mixin_of a1) -> Rel a1
op m =
  case m of {
   Mixin op0 _ -> op0}

type Type = Mixin_of Any
  -- singleton inductive, whose constructor was Pack
  
type Sort = Any

class0 :: Type -> Mixin_of Sort
class0 cT =
  cT

eq_op :: Type -> Rel Sort
eq_op t =
  op (class0 t)

eqP :: Type -> Axiom Sort
eqP t =
  let {_evar_0_ = \_ a -> a} in case t of {
                                 Mixin x x0 -> _evar_0_ x x0}

data SubType0 t =
   SubType (Any -> t) (t -> () -> Any) (() -> (t -> () -> Any) -> Any -> Any)

type Sub_sort t = Any

val :: (Pred a1) -> (SubType0 a1) -> (Sub_sort a1) -> a1
val _ s =
  case s of {
   SubType val0 _ _ -> val0}

sub0 :: (Pred a1) -> (SubType0 a1) -> a1 -> Sub_sort a1
sub0 _ s x =
  case s of {
   SubType _ sub1 _ -> sub1 x __}

insub :: (Pred a1) -> (SubType0 a1) -> a1 -> Option (Sub_sort a1)
insub p sT x =
  case idP (p x) of {
   ReflectT -> Some (sub0 p sT x);
   ReflectF -> None}

inj_eqAxiom :: Type -> (a1 -> Sort) -> Axiom a1
inj_eqAxiom eT f x y =
  iffP (eq_op eT (f x) (f y)) (eqP eT (f x) (f y))

val_eqP :: Type -> (Pred Sort) -> (SubType0 Sort) -> Axiom (Sub_sort Sort)
val_eqP t p sT =
  inj_eqAxiom t (val p sT)

eqn :: Nat -> Nat -> Prelude.Bool
eqn m n =
  case m of {
   O -> case n of {
         O -> Prelude.True;
         S _ -> Prelude.False};
   S m' -> case n of {
            O -> Prelude.False;
            S n' -> eqn m' n'}}

eqnP :: Axiom Nat
eqnP n m =
  iffP (eqn n m) (idP (eqn n m))

nat_eqMixin :: Mixin_of Nat
nat_eqMixin =
  Mixin eqn eqnP

nat_eqType :: Type
nat_eqType =
  unsafeCoerce nat_eqMixin

subn_rec :: Nat -> Nat -> Nat
subn_rec =
  sub

subn :: Nat -> Nat -> Nat
subn =
  subn_rec

leq :: Nat -> Nat -> Prelude.Bool
leq m n =
  eq_op nat_eqType (unsafeCoerce subn m n) (unsafeCoerce O)

filter :: (Pred a1) -> (([]) a1) -> ([]) a1
filter a s =
  case s of {
   [] -> [];
   (:) x s' ->
    case a x of {
     Prelude.True -> (:) x (filter a s');
     Prelude.False -> filter a s'}}

pmap :: (a1 -> Option a2) -> (([]) a1) -> ([]) a2
pmap f s =
  case s of {
   [] -> [];
   (:) x s' -> let {r = pmap f s'} in apply (\x0 -> (:) x0 r) r (f x)}

iota :: Nat -> Nat -> ([]) Nat
iota m n =
  case n of {
   O -> [];
   S n' -> (:) m (iota (S m) n')}

type Mixin_of0 t =
  (Pred t) -> Nat -> Option t
  -- singleton inductive, whose constructor was Mixin
  
find :: (Mixin_of0 a1) -> (Pred a1) -> Nat -> Option a1
find m =
  m

data Class_of t =
   Class (Mixin_of t) (Mixin_of0 t)

base :: (Class_of a1) -> Mixin_of a1
base c =
  case c of {
   Class base1 _ -> base1}

mixin :: (Class_of a1) -> Mixin_of0 a1
mixin c =
  case c of {
   Class _ mixin2 -> mixin2}

type Type0 = Class_of Any
  -- singleton inductive, whose constructor was Pack
  
type Sort0 = Any

class1 :: Type0 -> Class_of Sort0
class1 cT =
  cT

find0 :: Type0 -> (Pred Sort0) -> Nat -> Option Sort0
find0 t =
  find (mixin (class1 t))

pcanChoiceMixin :: Type0 -> (a1 -> Sort0) -> (Sort0 -> Option a1) ->
                   Mixin_of0 a1
pcanChoiceMixin t _ f' =
  let {liftP = \sP -> simplPred (\x -> apply sP Prelude.False (f' x))} in
  let {
   sf = \sP -> SimplFun (\n ->
    bind f' (find0 t (pred_of_simpl (liftP sP)) n))}
  in
  (\sP -> fun_of_simpl (sf sP))

sub_choiceMixin :: Type0 -> (Pred Sort0) -> (SubType0 Sort0) -> Mixin_of0
                   (Sub_sort Sort0)
sub_choiceMixin t p sT =
  pcanChoiceMixin t (val p sT) (insub p sT)

nat_choiceMixin :: Mixin_of0 Nat
nat_choiceMixin =
  let {
   f = \p -> SimplFun (\n ->
    case p n of {
     Prelude.True -> Some n;
     Prelude.False -> None})}
  in
  (\p -> fun_of_simpl (f p))

nat_choiceType :: Type0
nat_choiceType =
  Class (class0 nat_eqType) (unsafeCoerce nat_choiceMixin)

data Mixin_of1 t =
   Mixin0 (t -> Nat) (Nat -> Option t)

pickle :: (Mixin_of1 a1) -> a1 -> Nat
pickle m =
  case m of {
   Mixin0 pickle1 _ -> pickle1}

unpickle :: (Mixin_of1 a1) -> Nat -> Option a1
unpickle m =
  case m of {
   Mixin0 _ unpickle1 -> unpickle1}

data Class_of0 t =
   Class0 (Class_of t) (Mixin_of1 t)

mixin0 :: (Class_of0 a1) -> Mixin_of1 a1
mixin0 c =
  case c of {
   Class0 _ mixin2 -> mixin2}

type Type1 = Class_of0 Any
  -- singleton inductive, whose constructor was Pack
  
type Sort1 = Any

class2 :: Type1 -> Class_of0 Sort1
class2 cT =
  cT

unpickle0 :: Type1 -> Nat -> Option Sort1
unpickle0 t =
  unpickle (mixin0 (class2 t))

pickle0 :: Type1 -> Sort1 -> Nat
pickle0 t =
  pickle (mixin0 (class2 t))

pcanCountMixin :: Type1 -> (a1 -> Sort1) -> (Sort1 -> Option a1) -> Mixin_of1
                  a1
pcanCountMixin t f f' =
  Mixin0 (funcomp Tt (pickle0 t) f) (pcomp f' (unpickle0 t))

sub_countMixin :: Type1 -> (Pred Sort1) -> (SubType0 Sort1) -> Mixin_of1
                  (Sub_sort Sort1)
sub_countMixin t p sT =
  pcanCountMixin t (val p sT) (insub p sT)

nat_countMixin :: Mixin_of1 Nat
nat_countMixin =
  Mixin0 (\x -> x) (\x -> Some x)

nat_countType :: Type1
nat_countType =
  Class0 (class1 nat_choiceType) (unsafeCoerce nat_countMixin)

data Mixin_of2 =
   Mixin1 (Mixin_of1 Sort) (([]) Sort)

mixin_enum :: Type -> Mixin_of2 -> ([]) Sort
mixin_enum _ m =
  case m of {
   Mixin1 _ mixin_enum0 -> mixin_enum0}

data Class_of1 t =
   Class1 (Class_of t) Mixin_of2

base0 :: (Class_of1 a1) -> Class_of a1
base0 c =
  case c of {
   Class1 base1 _ -> base1}

mixin1 :: (Class_of1 a1) -> Mixin_of2
mixin1 c =
  case c of {
   Class1 _ mixin2 -> mixin2}

type Type2 = Class_of1 Any
  -- singleton inductive, whose constructor was Pack
  
type Sort2 = Any

class3 :: Type2 -> Class_of1 Sort2
class3 cT =
  cT

enum :: Type2 -> ([]) Sort
enum cT =
  mixin_enum (base (base0 (class3 cT))) (mixin1 (class3 cT))

enumDef :: ()
enumDef =
  __

enum_mem :: Type2 -> (Mem_pred Sort2) -> ([]) Sort2
enum_mem t mA =
  filter (pred_of_simpl (pred_of_mem_pred mA)) (enum t)

type Ordinal = Nat
  -- singleton inductive, whose constructor was Ordinal
  
nat_of_ord :: Nat -> Ordinal -> Nat
nat_of_ord _ i =
  i

ordinal_subType :: Nat -> SubType0 Nat
ordinal_subType n =
  SubType (unsafeCoerce nat_of_ord n) (unsafeCoerce (\x _ -> x)) (\_ k_S u ->
    k_S (unsafeCoerce u) __)

ordinal_eqMixin :: Nat -> Mixin_of Ordinal
ordinal_eqMixin n =
  Mixin (\x y ->
    eq_op nat_eqType (unsafeCoerce nat_of_ord n x)
      (unsafeCoerce nat_of_ord n y))
    (unsafeCoerce val_eqP nat_eqType (\x -> leq (S (unsafeCoerce x)) n)
      (ordinal_subType n))

ordinal_eqType :: Nat -> Type
ordinal_eqType n =
  unsafeCoerce ordinal_eqMixin n

ordinal_choiceMixin :: Nat -> Mixin_of0 Ordinal
ordinal_choiceMixin n =
  unsafeCoerce sub_choiceMixin nat_choiceType (\x ->
    leq (S (unsafeCoerce x)) n) (ordinal_subType n)

ordinal_choiceType :: Nat -> Type0
ordinal_choiceType n =
  Class (class0 (ordinal_eqType n)) (unsafeCoerce ordinal_choiceMixin n)

ordinal_countMixin :: Nat -> Mixin_of1 Ordinal
ordinal_countMixin n =
  unsafeCoerce sub_countMixin nat_countType (\x ->
    leq (S (unsafeCoerce x)) n) (ordinal_subType n)

ord_enum :: Nat -> ([]) Ordinal
ord_enum n =
  pmap (unsafeCoerce insub (\x -> leq (S x) n) (ordinal_subType n))
    (iota O n)

ordinal_finMixin :: Nat -> Mixin_of2
ordinal_finMixin n =
  Mixin1 (unsafeCoerce ordinal_countMixin n) (unsafeCoerce ord_enum n)

ordinal_finType :: Nat -> Type2
ordinal_finType n =
  Class1 (class1 (ordinal_choiceType n)) (ordinal_finMixin n)

type R = Prelude.Double

type AxVec t = [t]

type Float32 = Prelude.Float

type Float32_arr = AxVec Float32

f32_0 :: Float32
f32_0 = (0.0 :: Prelude.Float)

f32_1 :: Float32
f32_1 = (1.0 :: Prelude.Float)

f32_opp :: Float32 -> Float32
f32_opp = (\f -> - f)

f32_gt :: Float32 -> Float32 -> Prelude.Bool
f32_gt = (\f1 f2 -> (Prelude.>) f1 f2)

f32_add :: Float32 -> Float32 -> Float32
f32_add = (\f1 f2 -> (Prelude.+) f1 f2)

f32_mult :: Float32 -> Float32 -> Float32
f32_mult = (\f1 f2 -> (Prelude.*) f1 f2)

f32_fold2 :: Nat -> a1 -> (Float32 -> Float32 -> a1 -> a1) -> Float32_arr ->
             Float32_arr -> a1
f32_fold2 = (\_ t f a1 a2 -> Prelude.foldl (\acc (x, y) -> f x y acc) t (Prelude.zip a1 a2))

f32_get :: Nat -> Ordinal -> Float32_arr -> Float32
f32_get = (\_ i a -> (if (eqn i O) then (Prelude.head a) else (let (S x) = i in (f32_get O x (Prelude.tail a)))))

f32_upd :: Nat -> Ordinal -> Float32 -> Float32_arr -> Float32_arr
f32_upd = (\_ i new a -> (if (eqn i O) then ([new] Prelude.++ (Prelude.tail a)) else (let (S x) = i in ([Prelude.head a] Prelude.++ (f32_upd O x new (Prelude.tail a))))))

neg1 :: Float32
neg1 =
  f32_opp f32_1

float32_of_bool :: Prelude.Bool -> Float32
float32_of_bool b =
  case b of {
   Prelude.True -> f32_1;
   Prelude.False -> neg1}

f32_dot :: Nat -> Float32_arr -> Float32_arr -> Float32
f32_dot n a1 a2 =
  f32_fold2 n f32_0 (\x1 x2 sum -> f32_add (f32_mult x1 x2) sum) a1 a2

data Monad m =
   MkMonad (() -> Any -> m) (() -> () -> m -> (Any -> m) -> m)

ret :: (Monad a1) -> a2 -> a1
ret monad x =
  case monad of {
   MkMonad ret0 _ -> unsafeCoerce ret0 __ x}

bind0 :: (Monad a1) -> a1 -> (a2 -> a1) -> a1
bind0 monad m f =
  case monad of {
   MkMonad _ bind1 -> unsafeCoerce bind1 __ __ m f}

foldrM :: (Monad a1) -> (a2 -> a3 -> a1) -> a3 -> (([]) a2) -> a1
foldrM h f z0 s =
  case s of {
   [] -> ret h z0;
   (:) x s' -> bind0 h (foldrM h f z0 s') (\r -> f x r)}

type Id a = a

iret :: a1 -> Id a1
iret x =
  x

ibind :: (Id a1) -> (a1 -> Id a2) -> Id a2
ibind m f =
  f m

idMonad :: Monad (Id Any)
idMonad =
  MkMonad (\_ -> iret) (\_ _ -> ibind)

type Cont r a = (a -> r) -> r

cret :: a2 -> Cont a1 a2
cret x k =
  k x

cbind :: (Cont a1 a2) -> (a2 -> Cont a1 a3) -> Cont a1 a3
cbind m f k =
  m (\x -> f x k)

contMonad :: Monad (Cont a1 Any)
contMonad =
  MkMonad (\_ -> cret) (\_ _ -> cbind)

data Foldable t t0 =
   MkFoldable (() -> (Monad Any) -> () -> (t0 -> Any -> Any) -> Any -> t ->
              Any) (() -> (Monad Any) -> (t0 -> Any) -> t -> Any)

foldable_foldM :: (Foldable a1 a2) -> (Monad a3) -> (a2 -> a4 -> a3) -> a4 ->
                  a1 -> a3
foldable_foldM foldable h x x0 x1 =
  case foldable of {
   MkFoldable foldable_foldM0 _ ->
    unsafeCoerce foldable_foldM0 __ h __ x x0 x1}

list_foldM :: (Monad a2) -> (a1 -> a3 -> a2) -> a3 -> (([]) a1) -> a2
list_foldM h f r0 l =
  case l of {
   [] -> ret h r0;
   (:) x l' -> bind0 h (f x r0) (\r' -> list_foldM h f r' l')}

list_mapM :: (Monad a2) -> (a1 -> a2) -> (([]) a1) -> a2
list_mapM h f l =
  case l of {
   [] -> ret h [];
   (:) x l' ->
    bind0 h (f x) (\x' ->
      bind0 h (list_mapM h f l') (\l'' -> ret h ((:) x' l'')))}

list_Foldable :: Foldable (([]) a1) a1
list_Foldable =
  MkFoldable (\_ x _ -> list_foldM x) (\_ -> list_mapM)

data T x y hypers params =
   Mk (hypers -> params -> x -> y) (hypers -> ((,) x y) -> params -> params)

update :: (T a1 a2 a3 a4) -> a3 -> ((,) a1 a2) -> a4 -> a4
update t =
  case t of {
   Mk _ update0 -> update0}

noised_sample :: (a3 -> Cont a4 a3) -> ((((,) a1 a2) -> R) -> Cont a4 
                 a3) -> (((,) a1 a2) -> R) -> Cont a4 a3
noised_sample noise_model sample d =
  bind0 (unsafeCoerce contMonad) (sample d) noise_model

learn_func :: (T a1 a2 a4 a3) -> a4 -> Nat -> (Foldable a5 ((,) a1 a2)) -> a3
              -> a5 -> a3
learn_func learner0 h epochs h0 init t =
  foldrM (unsafeCoerce idMonad) (\_ p_epoch ->
    foldable_foldM h0 (unsafeCoerce idMonad) (\xy p ->
      ret (unsafeCoerce idMonad) (update learner0 h xy p)) p_epoch t) init
    (enum_mem (ordinal_finType epochs)
      (mem predPredType (sort_of_simpl_pred pred_of_argType)))

learn :: (T a1 a2 a4 a3) -> a4 -> Nat -> (Foldable a5 ((,) a1 a2)) -> a3 ->
         a5 -> Cont a6 a3
learn learner0 h epochs h0 init t f =
  f (learn_func learner0 h epochs h0 init t)

extractible_main :: (T a1 a2 a4 a3) -> a4 -> Nat -> (Foldable a5 ((,) a1 a2))
                    -> (a5 -> Cont a6 a5) -> ((((,) a1 a2) -> R) -> Cont 
                    a6 a5) -> (((,) a1 a2) -> R) -> a3 -> Cont a6 ((,) a3 a5)
extractible_main learner0 h epochs h0 noise_model sample d init =
  bind0 (unsafeCoerce contMonad)
    (noised_sample (unsafeCoerce noise_model) (unsafeCoerce sample) d) (\t ->
    bind0 (unsafeCoerce contMonad)
      (learn (unsafeCoerce learner0) h epochs h0 (unsafeCoerce init) t)
      (\p -> ret (unsafeCoerce contMonad) ((,) p t)))

type Ak = (,) Ordinal Float32_arr

type Bk = Prelude.Bool

type KernelParams = Float32_arr

kernel_predict :: Nat -> Nat -> (Foldable a1 ((,) Ak Bk)) -> a1 ->
                  KernelParams -> Ak -> Bk
kernel_predict n m h t w x =
  f32_gt
    (foldable_foldM h (unsafeCoerce idMonad) (\xi_yi _ ->
      case xi_yi of {
       (,) y yi ->
        case y of {
         (,) i xi ->
          case x of {
           (,) _ xj ->
            f32_mult (f32_mult (float32_of_bool yi) (f32_get m i w))
              (f32_dot n xi xj)}}}) f32_0 t) f32_0

type Params = KernelParams

kernel_update :: Nat -> Nat -> (Foldable a1 ((,) Ak Bk)) -> a1 -> ((,) 
                 Ak Bk) -> Params -> Params
kernel_update n m f t example_label p =
  case example_label of {
   (,) a label ->
    case a of {
     (,) i example ->
      case eqb (kernel_predict n m f t p ((,) i example)) label of {
       Prelude.True -> p;
       Prelude.False -> f32_upd m i (f32_add (f32_get m i p) f32_1) p}}}

learner :: Nat -> Nat -> (Foldable a1 ((,) Ak Bk)) -> a1 -> T Ak Bk () Params
learner n m f t =
  Mk (\_ -> kernel_predict n m f t) (\_ -> kernel_update n m f t)

kperceptron :: Nat -> Nat -> Nat -> (Foldable a1 ((,) Ak Bk)) -> a1 -> ((((,)
               Ak Bk) -> R) -> Cont a2 (([]) ((,) Ak Bk))) -> (((,) Ak 
               Bk) -> R) -> KernelParams -> Cont a2
               ((,) KernelParams (([]) ((,) Ak Bk)))
kperceptron n m epochs f t =
  extractible_main (learner n m f t) __ epochs list_Foldable (\t0 ->
    ret (unsafeCoerce contMonad) t0)

