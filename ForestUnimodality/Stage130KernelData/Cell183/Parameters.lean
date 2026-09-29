import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell183
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-16692969603224012031716939/10000000000000000000000000)
  B := (10226220314165516966919967/100000000000000000000000000)
  C := (2407211317625053675212099/500000000000000000000000000)
  dδ := (12565937779117539174755791/200000000000000000000000000)
  dM := (2743983349602055932421607/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1128977120472324102706807/100000000000000000000000), (7151730725486351580855171/2500000000000000000000000), (1395429440805397103275709/125000000000000000000000), (15239699688014825440518507/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
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
end ForestUnimodality.Stage130KernelData.Cell183
