import PscVerif.BHWindowChoice

example (F G : Fin 3 → Prop)
    (hF : ∀ i j, F i → F j → i = j)
    (hG : ∀ i j, G i → G j → i = j) :
    ∃ i : Fin 3, ¬F i ∧ ¬G i :=
  Psc.BHWindowChoice.exists_clean_slot F G hF hG

#print axioms Psc.BHWindowChoice.exists_clean_slot
