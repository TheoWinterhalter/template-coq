Declare Scope metacoq_scope.

Notation "'eta_compose'" := (fun g f x => g (f x)).

(* \circ *)
Notation "g ∘ f" := (eta_compose g f) (at level 40, left associativity).

Notation " ! " := (@False_rect _ _) : metacoq_scope.

(** "Incoherent" notion of equivalence, that we only apply to hProps actually. *)
Record isEquiv (A B : Type) :=
  { equiv : A -> B;
    equiv_inv : B -> A}.

Infix "<~>" := isEquiv (at level 90).

(* Use \sum to input ∑ in Company Coq (it is not a sigma Σ). *)
Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "( x ; y )" := (@existT _ _ x y).
Notation "( x ; y ; z )" := (x ; ( y ; z)).
Notation "( x ; y ; z ; t )" := (x ; ( y ; (z ; t))).
Notation "( x ; y ; z ; t ; u )" := (x ; ( y ; (z ; (t ; u)))).
Notation "( x ; y ; z ; t ; u ; v )" := (x ; ( y ; (z ; (t ; (u ; v))))).
Notation "x .π1" := (@projT1 _ _ x) (at level 3, format "x '.π1'").
Notation "x .π2" := (@projT2 _ _ x) (at level 3, format "x '.π2'").
