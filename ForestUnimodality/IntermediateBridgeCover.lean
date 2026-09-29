import ForestUnimodality.FiniteRectangleCover

/-! Exact geometry for intermediate size/activity/mean covers. These theorems
select a rectangle; actual forest inequalities and rank bounds remain explicit
premises and must be supplied by the independently checked graph proofs. -/
namespace ForestUnimodality.IntermediateBridgeCover

structure Rectangle extends FiniteRectangleCover.Rectangle where
  lowerOrder : ℕ
  orderCap : ℕ

def Rectangle.Contains (r : Rectangle) (n : ℕ) (q m : ℝ) : Prop :=
  r.lowerOrder≤n ∧ n≤r.orderCap ∧ r.toRectangle.Contains q m

structure Band (ι : Type*) extends FiniteRectangleCover.Strip ι where
  lowerOrder : ℕ
  orderCap : ℕ
  rank : ℕ
  parentStrip : ℕ

def Band.check {ι : Type*} (s : Band ι) (rectangles : ι→Rectangle) : Bool :=
  s.toStrip.check (fun i=>(rectangles i).toRectangle) &&
    (decide (0<s.qhi ∧ s.mlo≤s.rank/(2*s.qhi)) &&
      s.cells.all (fun i=>decide ((rectangles i).lowerOrder≤s.lowerOrder ∧
        s.orderCap≤(rectangles i).orderCap)))

theorem Band.check_sound {ι : Type*} (s : Band ι) (rectangles : ι→Rectangle)
    (hc : s.check rectangles=true) {n : ℕ} {q m : ℝ}
    (hn : s.lowerOrder≤n) (hN : n≤s.orderCap)
    (hq : q∈Set.Icc (s.qlo:ℝ) (s.qhi:ℝ))
    (hm : m∈Set.Icc (s.mlo:ℝ) (s.mhi:ℝ)) :
    ∃i∈s.cells,(rectangles i).Contains n q m := by
  have h : s.toStrip.check (fun i=>(rectangles i).toRectangle)=true ∧
      (0<s.qhi ∧ s.mlo≤s.rank/(2*s.qhi)) ∧
      ∀i∈s.cells,(rectangles i).lowerOrder≤s.lowerOrder ∧
        s.orderCap≤(rectangles i).orderCap := by
    simpa only [check,Bool.and_eq_true_iff,List.all_eq_true,decide_eq_true_eq] using hc
  obtain ⟨i,hi,hpoint⟩ := s.toStrip.check_sound (fun i=>(rectangles i).toRectangle) h.1 hq hm
  exact ⟨i,hi,(h.2.2 i hi).1.trans hn,hN.trans (h.2.2 i hi).2,hpoint⟩

theorem Band.mean_lower_of_rank {ι : Type*} (s : Band ι) (rectangles : ι→Rectangle)
    (hc : s.check rectangles=true) {k m : ℝ}
    (hrank : (s.rank:ℝ)≤k) (hmass : k≤2*(s.qhi:ℝ)*m) : (s.mlo:ℝ)≤m := by
  have h : s.toStrip.check (fun i=>(rectangles i).toRectangle)=true ∧
      (0<s.qhi ∧ s.mlo≤s.rank/(2*s.qhi)) ∧
      s.cells.all (fun i=>decide ((rectangles i).lowerOrder≤s.lowerOrder ∧
        s.orderCap≤(rectangles i).orderCap))=true := by
    simpa only [check,Bool.and_eq_true_iff,decide_eq_true_eq] using hc
  have hq : (0:ℝ)<s.qhi := by exact_mod_cast h.2.1.1
  have hlo : (s.mlo:ℝ)≤(s.rank:ℝ)/(2*(s.qhi:ℝ)) := by exact_mod_cast h.2.1.2
  apply hlo.trans
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(s.qhi:ℝ))).mpr
  nlinarith

theorem Band.property {ι : Type*} (s : Band ι) (rectangles : ι→Rectangle)
    (hc : s.check rectangles=true) {n : ℕ} {q m : ℝ} {P : Prop}
    (hn : s.lowerOrder≤n) (hN : n≤s.orderCap)
    (hq : q∈Set.Icc (s.qlo:ℝ) (s.qhi:ℝ)) (hm : (s.mlo:ℝ)≤m)
    (hparent : (s.mhi:ℝ)≤m→P)
    (hcell : ∀i∈s.cells,(rectangles i).Contains n q m→P) : P := by
  by_cases hp : (s.mhi:ℝ)≤m
  · exact hparent hp
  · obtain ⟨i,hi,hpoint⟩ := s.check_sound rectangles hc hn hN hq ⟨hm,(le_of_not_ge hp)⟩
    exact hcell i hi hpoint

structure ActivityCover (ι : Type*) where
  qlo : ℚ
  qhi : ℚ
  lowerOrder : ℕ
  orderCap : ℕ
  bands : List (Band ι)

def ActivityCover.check {ι : Type*} (c : ActivityCover ι) (rectangles : ι→Rectangle) : Bool :=
  FiniteRectangleCover.chainCheck (fun b : Band ι=>(b.qlo,b.qhi)) c.bands c.qlo c.qhi &&
    (c.bands.all (fun b=>decide (b.lowerOrder≤c.lowerOrder ∧ c.orderCap≤b.orderCap)) &&
      c.bands.all (fun b=>b.check rectangles))

theorem ActivityCover.check_sound {ι : Type*} (c : ActivityCover ι) (rectangles : ι→Rectangle)
    (hc : c.check rectangles=true) {n : ℕ} {q : ℝ}
    (hn : c.lowerOrder≤n) (hN : n≤c.orderCap)
    (hq : q∈Set.Icc (c.qlo:ℝ) (c.qhi:ℝ)) :
    ∃b∈c.bands,b.check rectangles=true ∧ b.lowerOrder≤n ∧ n≤b.orderCap ∧
      q∈Set.Icc (b.qlo:ℝ) (b.qhi:ℝ) := by
  have h : FiniteRectangleCover.chainCheck (fun b : Band ι=>(b.qlo,b.qhi)) c.bands c.qlo c.qhi=true ∧
      (∀b∈c.bands,b.lowerOrder≤c.lowerOrder ∧ c.orderCap≤b.orderCap) ∧
      ∀b∈c.bands,b.check rectangles=true := by
    simpa only [check,Bool.and_eq_true_iff,List.all_eq_true,decide_eq_true_eq] using hc
  obtain ⟨b,hb,hpoint⟩ := FiniteRectangleCover.chainCheck_sound _ c.bands h.1 hq
  exact ⟨b,hb,h.2.2 b hb,(h.2.1 b hb).1.trans hn,hN.trans (h.2.1 b hb).2,hpoint⟩

theorem ActivityCover.property {ι : Type*} (c : ActivityCover ι) (rectangles : ι→Rectangle)
    (hc : c.check rectangles=true) {n : ℕ} {q m k : ℝ} {P : Prop}
    (hn : c.lowerOrder≤n) (hN : n≤c.orderCap)
    (hq : q∈Set.Icc (c.qlo:ℝ) (c.qhi:ℝ)) (hm : 0≤m) (hmass : k≤2*q*m)
    (hrank : ∀b∈c.bands,q∈Set.Icc (b.qlo:ℝ) (b.qhi:ℝ)→(b.rank:ℝ)≤k)
    (hparent : ∀b∈c.bands,q∈Set.Icc (b.qlo:ℝ) (b.qhi:ℝ)→(b.mhi:ℝ)≤m→P)
    (hcell : ∀b∈c.bands,∀i∈b.cells,(rectangles i).Contains n q m→P) : P := by
  obtain ⟨b,hb,hbc,hbn,hbN,hbq⟩ := c.check_sound rectangles hc hn hN hq
  have hmul := mul_le_mul_of_nonneg_right hbq.2 hm
  have hbmass : k≤2*(b.qhi:ℝ)*m := by nlinarith
  have hlo := b.mean_lower_of_rank rectangles hbc (hrank b hb hbq) hbmass
  exact b.property rectangles hbc hbn hbN hbq hlo (hparent b hb hbq) (hcell b hb)

#print axioms Band.check_sound
#print axioms Band.mean_lower_of_rank
#print axioms Band.property
#print axioms ActivityCover.check_sound
#print axioms ActivityCover.property
end ForestUnimodality.IntermediateBridgeCover
