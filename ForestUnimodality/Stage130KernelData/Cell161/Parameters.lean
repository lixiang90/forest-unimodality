import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-1023968129966020782628533/625000000000000000000000)
  B := (5635596864758377760873387/50000000000000000000000000)
  C := (249335345532286081424167/50000000000000000000000000)
  dδ := (70311425178002373570507189/1000000000000000000000000000)
  dM := (13460435105647789322952379/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(65903356720456285344766911/10000000000000000000000000), (2702993728298443798507833/400000000000000000000000), (60948516281080465262220969/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23881/45156)
  hi := (95549/180624)
  vmin := (8128831175/32625029376)
  damping := (8128831175/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell161
