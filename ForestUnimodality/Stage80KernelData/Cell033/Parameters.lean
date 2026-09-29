import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 110
  A := (-7391485425256224594647847/50000000000000000000000000)
  B := (6834228267566294645618541/50000000000000000000000000)
  C := (-1667111732881595864697033/2000000000000000000000000)
  dδ := (9845202531434191217662999/50000000000000000000000000)
  dM := (28262639523400725528878841/10000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(10434120865712094072819127/1000000000000000000000000), (1290844393684340730033/32000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (841/1786)
  hi := (1687/3572)
  vmin := (794745/3189796)
  damping := (794745/3189796)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell033
