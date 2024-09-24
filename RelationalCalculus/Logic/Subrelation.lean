-- Work in progress, not useful yet.


-- We define a relational algebraic method of checking if relations are subsets using linear implication.

-- def subR (S R : Relation α β) : PropR :=
--   full {⋆} β ▹ R ⊸ S ▹ full β {⋆}

-- infixl : 80 "⊑" => subR -- Typed: \squb

-- theorem sdfdf {α β : Type u} (R S: Relation α β ) : proofR (R ⊑ S) = (R ≤ S) :=
-- by
-- -- have h1 : (TrueR ≤ R⊑S) ↔ R ≤ S := by
-- simp [ proofR]
-- simp [(· ≤ ·), proofR, (·⊑·), (·⊸·), eval, domain]
-- sorry

-- theorem sddfdf {α β : Type u} (R S: Relation α β ) : proofR (S ⊑ R) = (R ≤ S) :=
-- by
-- -- have h1 : (TrueR ≤ R⊑S) ↔ R ≤ S := by
-- simp [ proofR]
-- simp [(· ≤ ·), proofR, (·⊑·), (·⊸·), eval, domain]



-- -- rw [simp_proofR_le] at h1

-- -- , eq, (·⊑·), andR,(·⊸·)  ]


-- -- Having given a compositional definition of sub-relation we can give a compositional definition of equivalence
-- def equivR (R S: Relation α β) : PropR := andR (subR S R) (subR R S)
-- infixl: 30 "≡" => equivR -- Typed as: \==


-- theorem equivR_equiv (R S: Relation α β) : (proofR (R ≡ S)) = (R ≈ S) := by
-- simp [(·≈·), equivR, proofR, eq]
-- constructor
-- · simp
--   intro h1 h2
--   sorry

-- -- When R is an endoRelation the left selection of R is a subrelation of id.
-- theorem select_left_sub_id {α: Type u} (R: EndoRelation α ) : proofR ((selectLeft R)⊑(idR α)) := by sorry
-- -- simp [selectLeft, (·≈·), eq]

-- -- When R is an endoRelation the right selection of R is a subrelation of id.
-- theorem select_right_sub_id {α: Type u} (R: EndoRelation α ) : proofR ((selectRight R)⊑(idR α)) := by sorry


-- -- TODO
-- -- theorem sub_rel_iff_leq {S R : Relation α β} : S ⊑ R ≈ TrueR ↔ S ≤ R := sorry



-- Forall L, gets left selection and returns subset prop relations for if idR is subset of selection.
-- Recall that  a selection is always a subset of idR.
-- def totalImgL (R : Relation α β) : PropR :=
--   let Left := selectLeft R
--   idR ⊑ Left

--
-- def totalImgR (R : Relation α β) :PropR :=
--   let Right := selectRight R
--   idR ⊑ Right

-- Checks that R is total on right and left images
-- def totalImg (R : Relation α β) :PropR :=
--   totalImgR R ∧ totalImgL R
