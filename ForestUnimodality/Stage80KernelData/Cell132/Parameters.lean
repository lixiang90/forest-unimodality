import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 34
  A := (-45371828144982940251850323/500000000000000000000000000)
  B := (2162958039190209652558039/25000000000000000000000000)
  C := (41218408716094737109791879/5000000000000000000000000000)
  dδ := (5856080512856658842890667/50000000000000000000000000)
  dM := (4124658143942106294788097/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(55109515596592002495412999/10000000000000000000000000), (9005625002818216984223909/500000000000000000000000), (2569546712475133887210177/250000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1549/2954)
  hi := (2326/4431)
  vmin := (4896230/19633761)
  damping := (4896230/19633761)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell132
