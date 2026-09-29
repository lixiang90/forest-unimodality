import ForestUnimodality.FiniteData.Order02
import ForestUnimodality.FiniteData.Order03
import ForestUnimodality.FiniteData.Order04
import ForestUnimodality.FiniteData.Order05
import ForestUnimodality.FiniteData.Order06
import ForestUnimodality.FiniteData.Order07
import ForestUnimodality.FiniteData.Order08
import ForestUnimodality.FiniteData.Order09
import ForestUnimodality.FiniteData.Order10
import ForestUnimodality.FiniteData.Order11
import ForestUnimodality.FiniteData.Order12
import ForestUnimodality.FiniteData.Order13
import ForestUnimodality.FiniteData.Order14
import ForestUnimodality.FiniteData.Order15
import ForestUnimodality.FiniteData.Order16
import ForestUnimodality.FiniteData.Order17
import ForestUnimodality.FiniteData.Order18
import ForestUnimodality.FiniteData.Order19
import ForestUnimodality.FiniteData.Order20
import ForestUnimodality.FiniteData.Order21
import ForestUnimodality.FiniteData.Order22
import ForestUnimodality.FiniteData.Order23
import ForestUnimodality.FiniteData.Order24
import ForestUnimodality.FiniteData.Order25
import ForestUnimodality.FiniteData.Order26
import ForestUnimodality.FiniteData.Order27
import ForestUnimodality.FiniteData.Order28
import ForestUnimodality.FiniteData.Order29
import ForestUnimodality.FiniteData.Order30
import ForestUnimodality.FiniteData.Order31
import ForestUnimodality.FiniteData.Order32
import ForestUnimodality.FiniteData.Order33
import ForestUnimodality.FiniteData.Order34
import ForestUnimodality.FiniteData.Order35
import ForestUnimodality.FiniteData.Order36
import ForestUnimodality.FiniteData.Order37
import ForestUnimodality.FiniteData.Order38
import ForestUnimodality.FiniteData.Order39
import ForestUnimodality.FiniteData.Order40
import ForestUnimodality.FiniteData.Order41
import ForestUnimodality.FiniteData.Order42
import ForestUnimodality.FiniteData.Order43
import ForestUnimodality.FiniteData.Order44
import ForestUnimodality.FiniteData.Order45
import ForestUnimodality.FiniteData.Order46
import ForestUnimodality.FiniteData.Order47
import ForestUnimodality.FiniteData.Order48
import ForestUnimodality.FiniteData.Order49
import ForestUnimodality.FiniteData.Order50
import ForestUnimodality.FiniteData.Order51
import ForestUnimodality.FiniteData.Order52
import ForestUnimodality.FiniteData.Order53
import ForestUnimodality.FiniteData.Order54
import ForestUnimodality.FiniteData.Order55
import ForestUnimodality.FiniteData.Order56
import ForestUnimodality.FiniteData.Order57
import ForestUnimodality.FiniteData.Order58
import ForestUnimodality.FiniteData.Order59
import ForestUnimodality.FiniteData.Order60

/-! Complete finite parameter coverage. This proves only the n ≤ 60 range;
the all-orders CompleteTarget also needs the separate large-order theorem. -/
namespace ForestUnimodality
open FiniteRows

theorem finite_domain_witnesses (n a k : ℕ) (h : Domain n a k) :
    ∃ w : Witness, w.check n a k = true := by
  have hnlo : 2 ≤ n := h.1
  have hnhi : n ≤ 60 := h.2.1
  interval_cases n

  · exact FiniteData.coverage_2 a k h
  · exact FiniteData.coverage_3 a k h
  · exact FiniteData.coverage_4 a k h
  · exact FiniteData.coverage_5 a k h
  · exact FiniteData.coverage_6 a k h
  · exact FiniteData.coverage_7 a k h
  · exact FiniteData.coverage_8 a k h
  · exact FiniteData.coverage_9 a k h
  · exact FiniteData.coverage_10 a k h
  · exact FiniteData.coverage_11 a k h
  · exact FiniteData.coverage_12 a k h
  · exact FiniteData.coverage_13 a k h
  · exact FiniteData.coverage_14 a k h
  · exact FiniteData.coverage_15 a k h
  · exact FiniteData.coverage_16 a k h
  · exact FiniteData.coverage_17 a k h
  · exact FiniteData.coverage_18 a k h
  · exact FiniteData.coverage_19 a k h
  · exact FiniteData.coverage_20 a k h
  · exact FiniteData.coverage_21 a k h
  · exact FiniteData.coverage_22 a k h
  · exact FiniteData.coverage_23 a k h
  · exact FiniteData.coverage_24 a k h
  · exact FiniteData.coverage_25 a k h
  · exact FiniteData.coverage_26 a k h
  · exact FiniteData.coverage_27 a k h
  · exact FiniteData.coverage_28 a k h
  · exact FiniteData.coverage_29 a k h
  · exact FiniteData.coverage_30 a k h
  · exact FiniteData.coverage_31 a k h
  · exact FiniteData.coverage_32 a k h
  · exact FiniteData.coverage_33 a k h
  · exact FiniteData.coverage_34 a k h
  · exact FiniteData.coverage_35 a k h
  · exact FiniteData.coverage_36 a k h
  · exact FiniteData.coverage_37 a k h
  · exact FiniteData.coverage_38 a k h
  · exact FiniteData.coverage_39 a k h
  · exact FiniteData.coverage_40 a k h
  · exact FiniteData.coverage_41 a k h
  · exact FiniteData.coverage_42 a k h
  · exact FiniteData.coverage_43 a k h
  · exact FiniteData.coverage_44 a k h
  · exact FiniteData.coverage_45 a k h
  · exact FiniteData.coverage_46 a k h
  · exact FiniteData.coverage_47 a k h
  · exact FiniteData.coverage_48 a k h
  · exact FiniteData.coverage_49 a k h
  · exact FiniteData.coverage_50 a k h
  · exact FiniteData.coverage_51 a k h
  · exact FiniteData.coverage_52 a k h
  · exact FiniteData.coverage_53 a k h
  · exact FiniteData.coverage_54 a k h
  · exact FiniteData.coverage_55 a k h
  · exact FiniteData.coverage_56 a k h
  · exact FiniteData.coverage_57 a k h
  · exact FiniteData.coverage_58 a k h
  · exact FiniteData.coverage_59 a k h
  · exact FiniteData.coverage_60 a k h

variable {V : Type*} [DecidableEq V]

theorem countIndependent_unimodal_of_isAcyclic_card_le_sixty
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (hn : S.card ≤ 60) :
    WeaklyUnimodal (countIndependent G S) :=
  countIndependent_unimodal_of_domain_witnesses finite_domain_witnesses G hG S hn

theorem independentCount_unimodal_of_isAcyclic_card_le_sixty
    {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic) (hn : n ≤ 60) :
    WeaklyUnimodal (independentCount G) :=
  independentCount_unimodal_of_domain_witnesses finite_domain_witnesses G hG hn

#print axioms finite_domain_witnesses
#print axioms countIndependent_unimodal_of_isAcyclic_card_le_sixty
#print axioms independentCount_unimodal_of_isAcyclic_card_le_sixty
end ForestUnimodality
