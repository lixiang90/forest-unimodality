import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 117
  A := (2788677745125241441925823/25000000000000000000000000)
  B := (91965070708581245217949629/1000000000000000000000000000)
  C := (33153639345304353192034341/50000000000000000000000000)
  dδ := (14462273334299036164907193/100000000000000000000000000)
  dM := (3952004705477691086021319/2500000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(63550384736194720503021927/10000000000000000000000000), (42092751340969121187640667/10000000000000000000000000), (5449568532732366854531847/250000000000000000000000), (21951820622103209501574383/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95699/180624)
  hi := (7977/15052)
  vmin := (56437275/226562704)
  damping := (56437275/226562704)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell144
