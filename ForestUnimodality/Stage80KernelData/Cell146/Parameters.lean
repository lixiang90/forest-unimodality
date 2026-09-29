import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (52667213180552170271653267/100000000000000000000000000)
  B := (49995119979853480662868037/1000000000000000000000000000)
  C := (65037298578333041509935697/10000000000000000000000000000)
  dδ := (11919081892124895605267199/100000000000000000000000000)
  dM := (13908948191975996702685059/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2389636622855308978330413/2000000000000000000000000), (6139194867503716679379977/1000000000000000000000000), (32079981863810722586549673/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23607/44732)
  hi := (94453/178928)
  vmin := (7978917175/32015229184)
  damping := (7978917175/32015229184)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell146
