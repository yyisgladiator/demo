definition monofun :: "('a ⇒ 'b) ⇒ bool"  ― ‹monotonicity›
  where "monofun f ⟷ (∀x y. x ⊑ y ⟶ f x ⊑ f y)"