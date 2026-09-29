import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 24
  A := (13160626767239109625506899/100000000000000000000000000)
  B := (23123311678477066755110769/1000000000000000000000000000)
  C := (-24567762317276808925470277/500000000000000000000000000)
  dδ := (23895336123698613511878719/1000000000000000000000000000)
  dM := (4145293174655741890236027/20000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(40338007902125183612440651/50000000000000000000000000), (74400605429892792130885937/10000000000000000000000000)]
  retention := ![(3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1/3)
  hi := (29/85)
  vmin := (2/9)
  damping := (80000000000000000000000000000000000000000/888264396098042275699264258736843725914681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell011
