import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell108.Parameters
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch000_049
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch050_099
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch100_149
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch150_199
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch000_049
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch050_099
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch100_149
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree000.table
  base := (889414357185739920430478379/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (178)
      previous := (89)
      next := (89)
      square := (616111408716545350117144150000000000000)
      linear := (-30368594456576833255645465000000000000)
      constant := (889414357185739920430478379000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree000.table
  base := (889414357185739920430478379/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (178)
      previous := (89)
      next := (89)
      square := (616111408716545350117144150000000000000)
      linear := (-30368594456576833255645465000000000000)
      constant := (889414357185739920430478379000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree001.table
  base := (243962389244243715973185849043440011070021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-4952534446960862496745626821759303750000000000)
      constant := (3603249584292327500087506445437750875720698007738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree001.table
  base := (487481644099195374989864620454783500240889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-4957765617890496414608965198807897500000000000)
      constant := (3599981176413227045845826506391862646228514037121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9991688896166689071/20000000000000000000)
  directionHi := (12489611120208361339/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree002.table
  base := (283435039596882223565879528766230883865151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-9680885226838368175059919068442222500000000000)
      constant := (2097491400798655265239655862135496885959958680439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree002.table
  base := (282984866180992234401832597285549428880301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-9691347568697636010786595822539410000000000000)
      constant := (2094179321215230671966248701210058546018552328789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9991688896166689071/20000000000000000000)
  centralHi := (12489611120208361339/25000000000000000000)
  directionLo := (35325954869928977883/50000000000000000000)
  directionHi := (70651909739857955767/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree003.table
  base := (176730637700475520713142297301915834366603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-14409236006715873853374211315125141250000000000)
      constant := (1316051102304421935067225331624745020076959473667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree003.table
  base := (176379860490147818591127028860655249081547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-14424929519504775606964226446270922500000000000)
      constant := (1313486506768096610057915111465557276255898211683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35325954869928977883/50000000000000000000)
  centralHi := (70651909739857955767/100000000000000000000)
  directionLo := (43265282053956244873/50000000000000000000)
  directionHi := (86530564107912489747/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree004.table
  base := (5947934525997960508311343191089856412709/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-19137586786593379531688503561808060000000000000)
      constant := (898292363917252159343827663319925821341771382020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree004.table
  base := (118707323765987618214323018761827182103313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-19158511470311915203141857070002435000000000000)
      constant := (896480799023535432116331586982880575905863760857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/50000000000000000000)
  centralHi := (86530564107912489747/100000000000000000000)
  directionLo := (99916888961666890711/100000000000000000000)
  directionHi := (12489611120208361339/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree005.table
  base := (85999807343394852401589218942593737647211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-23865937566470885210002795808490978750000000000)
      constant := (666163696775843014985543384536823629927799703779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree005.table
  base := (42911293645305522329820324515521305557651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-23892093421119054799319487693733947500000000000)
      constant := (664924104630489099856952324983207223514298625878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99916888961666890711/100000000000000000000)
  centralHi := (12489611120208361339/12500000000000000000)
  directionLo := (11171047790929277323/10000000000000000000)
  directionHi := (111710477909292773231/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree006.table
  base := (4117955710565701609065383968719529415853/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-28594288346348390888317088055173897500000000000)
      constant := (531325880053799269514822969094429436693867710672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree006.table
  base := (3287982029640934744145860656754770313013/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-28625675371926194395497118317465460000000000000)
      constant := (530482269315631683260897295357528113129396483140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11171047790929277323/10000000000000000000)
  centralHi := (111710477909292773231/100000000000000000000)
  directionLo := (61186348660602199773/50000000000000000000)
  directionHi := (122372697321204399547/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree007.table
  base := (10528729284045241913488381713613512698959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-33322639126225896566631380301856816250000000000)
      constant := (449652504977546141958502831212315054192665226755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree007.table
  base := (13136915292242494475521645083446454823261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-33359257322733333991674748941196972500000000000)
      constant := (449078149953885515685956917096052825427917888916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61186348660602199773/50000000000000000000)
  centralHi := (122372697321204399547/100000000000000000000)
  directionLo := (33044404995978161963/25000000000000000000)
  directionHi := (132177619983912647853/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree008.table
  base := (2162339762220264354367764333145271768141/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-38050989906103402244945672548539735000000000000)
      constant := (398834328304145995644137923104354152432084530980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree008.table
  base := (431708954539320874649526626290995382243/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-38092839273540473587852379564928485000000000000)
      constant := (398449185325372924558663223145607886030684562700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33044404995978161963/25000000000000000000)
  centralHi := (132177619983912647853/100000000000000000000)
  directionLo := (141303819479715911533/100000000000000000000)
  directionHi := (70651909739857955767/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree009.table
  base := (36139580785585070773693267666543183032223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-42779340685980907923259964795222653750000000000)
      constant := (367376278059203839515709376805387483823097553847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree009.table
  base := (36076741900178600316728841802731225368913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-42826421224347613184030010188659997500000000000)
      constant := (367133932624716123560511721809641862971123599257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141303819479715911533/100000000000000000000)
  centralHi := (70651909739857955767/50000000000000000000)
  directionLo := (149875333442500336067/100000000000000000000)
  directionHi := (37468833360625084017/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree010.table
  base := (30495887270848351412965879244823357114877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-47507691465858413601574257041905572500000000000)
      constant := (349179894082741045527614215937127016969555238053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree010.table
  base := (1217680052534697085047703454465330104873/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-47560003175154752780207640812391510000000000000)
      constant := (349055462134553512802467206801174284338795492425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149875333442500336067/100000000000000000000)
  centralHi := (37468833360625084017/25000000000000000000)
  directionLo := (78991236459250935969/50000000000000000000)
  directionHi := (157982472918501871939/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree011.table
  base := (1616149133941961148224136340495743828783/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-431702828477156357685029332963541250000000000)
      constant := (2817100299701062004040555872333800449941052752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree011.table
  base := (25811088077625632561881756565488706191109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-432178389470759441127151003604322500000000000)
      constant := (2816947109846208851044889772121890944763368981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78991236459250935969/50000000000000000000)
  centralHi := (157982472918501871939/100000000000000000000)
  directionLo := (82846707726363054179/50000000000000000000)
  directionHi := (165693415452726108359/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree012.table
  base := (878362048706380922851014002602122802183/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-56964393025613424958202841535271410000000000000)
      constant := (340465411453458233312790763511579400991107507175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree012.table
  base := (5479242177710958412144562468202588863307/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-57027167076769031972562902059854535000000000000)
      constant := (340548082164318025224260261313980494077364433292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82846707726363054179/50000000000000000000)
  centralHi := (165693415452726108359/100000000000000000000)
  directionLo := (43265282053956244873/25000000000000000000)
  directionHi := (173061128215824979493/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree013.table
  base := (18629686519818947079873674762392424009437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-365045821334265861754539253147658750000000000)
      constant := (2051639538439410449949356691813049684093717597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree013.table
  base := (9295995795913022069232957818577484595281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-365448219098083855436334512920627500000000000)
      constant := (2052723600974382950424840968955135427962938722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/25000000000000000000)
  centralHi := (173061128215824979493/100000000000000000000)
  directionLo := (22515966652258240663/12500000000000000000)
  directionHi := (36025546643613185061/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree014.table
  base := (15756880821656087058155547967382430469563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-66421094585368436314831426028637247500000000000)
      constant := (358816936114325333577558186587100356731375857107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree014.table
  base := (1572303457052269656105155764188262353951/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-66494330978383311164918163307317560000000000000)
      constant := (359102141712912089690359601379361785147157836390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22515966652258240663/12500000000000000000)
  centralHi := (36025546643613185061/20000000000000000000)
  directionLo := (93463691411723151997/50000000000000000000)
  directionHi := (37385476564689260799/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree015.table
  base := (828685317203092841293201104638592269717/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-71149445365245941993145718275320166250000000000)
      constant := (376132085627351671311057507968878728602143881008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree015.table
  base := (3307144548749630812171526131340709817501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-71227912929190450761095793931049072500000000000)
      constant := (376521857759624770268536828632904804752614558356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93463691411723151997/50000000000000000000)
  centralHi := (37385476564689260799/20000000000000000000)
  directionLo := (48372055869173943751/25000000000000000000)
  directionHi := (38697644695339155001/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree016.table
  base := (5536963959034271565345308669707746709199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-75877796145123447671460010522003085000000000000)
      constant := (398214757138127231043190019521833515393528273422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree016.table
  base := (11046687573408263514458483242129323087919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-75961494879997590357273424554780585000000000000)
      constant := (398712227821001671737351129206913722544772882791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48372055869173943751/25000000000000000000)
  centralHi := (38697644695339155001/20000000000000000000)
  directionLo := (99916888961666890711/50000000000000000000)
  directionHi := (199833777923333781423/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree017.table
  base := (9152838216887685504602418887250435067977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-80606146925000953349774302768686003750000000000)
      constant := (424703736666309964269683661322756300671464763953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree017.table
  base := (9128471529636756667373291174779869963217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-80695076830804729953451055178512097500000000000)
      constant := (425312332883646003626572942388892512195644620313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99916888961666890711/50000000000000000000)
  centralHi := (199833777923333781423/100000000000000000000)
  directionLo := (1287399646787699647/625000000000000000)
  directionHi := (205983943486031943521/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree018.table
  base := (7456075845780770402599557615983936811257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-85334497704878459028088595015368922500000000000)
      constant := (455306544916121881992401037134656023329825375873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree018.table
  base := (1858583210114267849436921957479146605933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-85428658781611869549628685802243610000000000000)
      constant := (456029862721543691811236977883774011681181336148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1287399646787699647/625000000000000000)
  centralHi := (205983943486031943521/100000000000000000000)
  directionLo := (2119557292195738673/1000000000000000000)
  directionHi := (211955729219573867301/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree019.table
  base := (29755138524804841258471783353327181777/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-249481574750016522732417970254991250000000000)
      constant := (1356738030699087887190346594213428093969074600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree019.table
  base := (1482918538083264075353906784589672810011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-249756899535786728935751569047022500000000000)
      constant := (1359069752824726875092283969060292345917659756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2119557292195738673/1000000000000000000)
  centralHi := (211955729219573867301/100000000000000000000)
  directionLo := (217763810868440298361/100000000000000000000)
  directionHi := (108881905434220149181/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree020.table
  base := (4610575131301557890729241003891169615929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-94791199264633470384717179508734760000000000000)
      constant := (527931196780294026229777349427817051043883695681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree020.table
  base := (4593390125769685912525316634454222205967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-94895822683226148741983947049706635000000000000)
      constant := (528895192999666640871621154438894859750224725063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217763810868440298361/100000000000000000000)
  centralHi := (108881905434220149181/50000000000000000000)
  directionLo := (223420955818585546461/100000000000000000000)
  directionHi := (111710477909292773231/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree021.table
  base := (1706015029367637812916702292537139715087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-99519550044510976063031471755417678750000000000)
      constant := (569585362686945358279964679265435648887851253486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree021.table
  base := (679361127033039607123958834484537277351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-99629404634033288338161577673438147500000000000)
      constant := (570675509616086021617458212478379406994863831195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223420955818585546461/100000000000000000000)
  centralHi := (111710477909292773231/50000000000000000000)
  directionLo := (4578767068713361509/2000000000000000000)
  directionHi := (228938353435668075451/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree022.table
  base := (1168170994509161286792596129752639104153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-861552899375111419349964991752897500000000000)
      constant := (5079374333295823606369899397888670486960540754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree022.table
  base := (14518021469308146329254875826919623211/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-862504021362317586234208333034460000000000000)
      constant := (5089459470900027318573477546841411911796783840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4578767068713361509/2000000000000000000)
  centralHi := (228938353435668075451/100000000000000000000)
  directionLo := (58581468832291256309/25000000000000000000)
  directionHi := (234325875329165025237/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree023.table
  base := (683740177798337798297772959049612999793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-108976251604265987419660056248783516250000000000)
      constant := (662869652636819698393891538477660755870995315154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree023.table
  base := (1355606594347515350263225630091955428507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-109096568535647567530516838920901172500000000000)
      constant := (664224213676533915581091799036035128626021811123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58581468832291256309/25000000000000000000)
  centralHi := (234325875329165025237/100000000000000000000)
  directionLo := (119796141448424694203/50000000000000000000)
  directionHi := (239592282896849388407/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree024.table
  base := (98387743327213835871767698461489379187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-113704602384143493097974348495466435000000000000)
      constant := (714281731855326613064272394243995103348565908215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree024.table
  base := (481482504203793010599785127552742752047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-113830150486454707126694469544632685000000000000)
      constant := (715774759070446220746528154026126914189715886183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119796141448424694203/50000000000000000000)
  centralHi := (239592282896849388407/100000000000000000000)
  directionLo := (244745394642408799093/100000000000000000000)
  directionHi := (122372697321204399547/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree025.table
  base := (-301671145184950094200072428693297496423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-118432953164020998776288640742149353750000000000)
      constant := (768756463150497089655079662479160462263865732353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree025.table
  base := (-77715819786285635186713487912694790139/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-118563732437261846722872100168364197500000000000)
      constant := (770392265004158917457858441778722950536180318516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244745394642408799093/100000000000000000000)
  centralHi := (122372697321204399547/50000000000000000000)
  directionLo := (124896111202083613389/50000000000000000000)
  directionHi := (249792222404167226779/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree026.table
  base := (-511477805577260532641256318633364169147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-728765112094073990855638656738652500000000000)
      constant := (4888893084974521612995315321100191258204979786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree026.table
  base := (-1031023669274289077202920606397977693641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-729569907621709978219229176284590000000000000)
      constant := (4899443288378059550158866301122573061364067479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124896111202083613389/50000000000000000000)
  centralHi := (249792222404167226779/100000000000000000000)
  directionLo := (254739083276511500391/100000000000000000000)
  directionHi := (31842385409563937549/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree027.table
  base := (-840010044362992648709598102918418830303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-127889654723776010132917225235515191250000000000)
      constant := (886621301646715971118275389088124329559292214066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree027.table
  base := (-1687091113792198767093764309019925491697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-128030896338876125915227361415827222500000000000)
      constant := (888555972097171491035777332598251588965673984967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254739083276511500391/100000000000000000000)
  centralHi := (31842385409563937549/12500000000000000000)
  directionLo := (129795846161868734619/50000000000000000000)
  directionHi := (259591692323737469239/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree028.table
  base := (-1139852279589070831494667837091173283939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-132618005503653515811231517482198110000000000000)
      constant := (949901080658004118132277973227173923532080062858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree028.table
  base := (-2285893291569769638274665685186473311007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-132764478289683265511404992039558735000000000000)
      constant := (951992031554908809883093064205662652422021646377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129795846161868734619/50000000000000000000)
  centralHi := (259591692323737469239/100000000000000000000)
  directionLo := (33044404995978161963/12500000000000000000)
  directionHi := (52871047993565059141/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree029.table
  base := (-706945411017615838286537442104295119219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-137346356283531021489545809728881028750000000000)
      constant := (1016019654388443243748008968410441482989076426036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree029.table
  base := (-2833191279189992707345191364523832254563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-137498060240490405107582622663290247500000000000)
      constant := (1018271565329032564948057121490617310644495277893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33044404995978161963/12500000000000000000)
  centralHi := (52871047993565059141/20000000000000000000)
  directionLo := (53806891407473453627/20000000000000000000)
  directionHi := (33629307129670908517/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree030.table
  base := (-41614042678479196593242806993297161033/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-142074707063408527167860101975563947500000000000)
      constant := (1084941056777216945331827212151417291773314965040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree030.table
  base := (-208365401107905222305907167948003945017/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-142231642191297544703760253287021760000000000000)
      constant := (1087358686567077970448209376419803890713534391792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53806891407473453627/20000000000000000000)
  centralHi := (33629307129670908517/12500000000000000000)
  directionLo := (13681683490010972707/5000000000000000000)
  directionHi := (273633669800219454141/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree031.table
  base := (-3787842003222827576528204691389218991827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-146803057843286032846174394222246866250000000000)
      constant := (1156634931689431018596408193572624731097780313397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree031.table
  base := (-947990237461926502487635613290787682321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-146965224142104684299937883910753272500000000000)
      constant := (1159223112148566828948677571511592492764760605724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13681683490010972707/5000000000000000000)
  centralHi := (273633669800219454141/100000000000000000000)
  directionLo := (278156846802806653223/100000000000000000000)
  directionHi := (34769605850350831653/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree032.table
  base := (-2103704100958546267182731530239453020191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-151531408623163538524488686468929785000000000000)
      constant := (1231075657436925963244794719599097302987262482002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree032.table
  base := (-4210996612791824818690433946724479725663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-151698806092911823896115514534484785000000000000)
      constant := (1233839287221112394052226973162728852186460149993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278156846802806653223/100000000000000000000)
  centralHi := (34769605850350831653/12500000000000000000)
  directionLo := (282607638959431823067/100000000000000000000)
  directionHi := (70651909739857955767/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree033.table
  base := (-286921969699376540725597240778652217473/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-1291402970273066481014900650542253750000000000)
      constant := (10811914116977925236558710231852132958264535888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree033.table
  base := (-4593874673440336690652463160412156240117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-1292829653253875731341265662464597500000000000)
      constant := (10836245014319030616616554312840900228696701947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282607638959431823067/100000000000000000000)
  centralHi := (70651909739857955767/25000000000000000000)
  directionLo := (286989414043739748069/100000000000000000000)
  directionHi := (28698941404373974807/10000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree034.table
  base := (-4940344592730764583868148292621573935459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-160988110182918549881117270962295622500000000000)
      constant := (1388114530521568931079621715162333449607111406149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree034.table
  base := (-4943060324800530157940739205317736166429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-161165969994526103088470775781947810000000000000)
      constant := (1391243992408855779031133976860863966465902309819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286989414043739748069/100000000000000000000)
  centralHi := (28698941404373974807/10000000000000000000)
  directionLo := (291305286509039521539/100000000000000000000)
  directionHi := (14565264325451976077/5000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree035.table
  base := (-2629137241396246888918220423333077211603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-165716460962796055559431563208978541250000000000)
      constant := (1470679017762693615640195325213150537533587142666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree035.table
  base := (-5260633896259945852366663105026799647839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-165899551945333242684648406405679322500000000000)
      constant := (1473998967073183476878671694613274116833233844329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291305286509039521539/100000000000000000000)
  centralHi := (14565264325451976077/5000000000000000000)
  directionLo := (295558143388163339591/100000000000000000000)
  directionHi := (36944767923520417449/12500000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree036.table
  base := (-2773151384504651708290089075128679137781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-170444811742673561237745855455661460000000000000)
      constant := (1555922065710535202757818148454806408929914790982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree036.table
  base := (-1109670188318065738715441998683615928049/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-170633133896140382280826037029410835000000000000)
      constant := (1559437611071398491471084406091899656886623428195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295558143388163339591/100000000000000000000)
  centralHi := (36944767923520417449/12500000000000000000)
  directionLo := (149875333442500336067/50000000000000000000)
  directionHi := (59950133377000134427/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree037.table
  base := (-5805916326665022325464565834849951799331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-175173162522551066916060147702344378750000000000)
      constant := (1643832698119416567782878779412600779445065917541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree037.table
  base := (-5807692943724311471777548521227712124591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-175366715846947521877003667653142347500000000000)
      constant := (1647548987964640146546759228056996515298640149401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149875333442500336067/50000000000000000000)
  centralHi := (59950133377000134427/20000000000000000000)
  directionLo := (75971338539999394089/25000000000000000000)
  directionHi := (303885354159997576357/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree038.table
  base := (-1207674032519309571473621633124055327709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-498342142111990505801591246396197500000000000)
      constant := (4804436704756709490228708292005878931768393295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree038.table
  base := (-3019955051243700630010462165185118824391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-498892791683530918208258443980260000000000000)
      constant := (4815301575253542283718248197897754635320056882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75971338539999394089/25000000000000000000)
  centralHi := (303885354159997576357/100000000000000000000)
  directionLo := (307964534724197867373/100000000000000000000)
  directionHi := (153982267362098933687/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree039.table
  base := (-195147611684349899020937054522900564253/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-1092484402853882119956738060329646250000000000)
      constant := (10814326051942998861231304505959284797929170624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree039.table
  base := (-6246057441905707606630861208482853965333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-1093691596145336101002123839648552500000000000)
      constant := (10838783815951517550817724655918482174690289227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307964534724197867373/100000000000000000000)
  centralHi := (153982267362098933687/50000000000000000000)
  directionLo := (62398077157180474053/20000000000000000000)
  directionHi := (155995192892951185133/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree040.table
  base := (-642587066764662240935041111941505223281/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-189358214862183583951003024442393135000000000000)
      constant := (1923484454825007373924757006429041356477747859910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree040.table
  base := (-3213512640162059480387375756220093936601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-189567461699368940665536559524336885000000000000)
      constant := (1927834204243212952317657164008030450943302121022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62398077157180474053/20000000000000000000)
  centralHi := (155995192892951185133/50000000000000000000)
  directionLo := (78991236459250935969/25000000000000000000)
  directionHi := (315964945837003743877/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree041.table
  base := (-6582566121144535601811588243916210962543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-194086565642061089629317316689076053750000000000)
      constant := (2021986135462056787603327064793469213967669407673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree041.table
  base := (-3291782471770832712296502067843584766493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-194301043650176080261714190148068397500000000000)
      constant := (2026557540354831786782993101966708322568158912246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78991236459250935969/25000000000000000000)
  centralHi := (315964945837003743877/100000000000000000000)
  directionLo := (319890126719667962989/100000000000000000000)
  directionHi := (31989012671966796299/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree042.table
  base := (-1343089385000005543397076977308800910297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-198814916421938595307631608935758972500000000000)
      constant := (2123121442368161336052449575798523806453282647835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree042.table
  base := (-6716310463676731473154688477195610182723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-199034625600983219857891820771799910000000000000)
      constant := (2127919792749136196753025129275870683346832551653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319890126719667962989/100000000000000000000)
  centralHi := (31989012671966796299/10000000000000000000)
  directionLo := (16188386218804342649/5000000000000000000)
  directionHi := (323767724376086852981/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree043.table
  base := (-1706262683873530259526807166618512860271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-203543267201816100985945901182441891250000000000)
      constant := (2226886406516803103766297404806392611969777155524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree043.table
  base := (-3412898445243266912553494521779395098691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-203768207551790359454069451395531422500000000000)
      constant := (2231917011641198980018411770308424850749348509002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16188386218804342649/5000000000000000000)
  centralHi := (323767724376086852981/100000000000000000000)
  directionLo := (163799714226409948513/50000000000000000000)
  directionHi := (327599428452819897027/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree044.table
  base := (-691183136502906751539350078869864107833/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-1721253041171021542679836309331610000000000000)
      constant := (19283286593590407959073964103337977731452165030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree044.table
  base := (-1728118936001191924648741156697783882887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-1723155285145433876448322991894735000000000000)
      constant := (19326825321239224094875469307037089612355788068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163799714226409948513/50000000000000000000)
  centralHi := (327599428452819897027/100000000000000000000)
  directionLo := (82846707726363054179/25000000000000000000)
  directionHi := (331386830905452216717/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree045.table
  base := (-3488085928477100463582475070955675804219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-212999968761571112342574485675807728750000000000)
      constant := (2442292428630974473855136292048044799464655033018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree045.table
  base := (-6976728054788290325609512482267832171309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-213235371453404638646424712642994447500000000000)
      constant := (2447803536633895163490734726076024309043083715499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82846707726363054179/25000000000000000000)
  centralHi := (331386830905452216717/100000000000000000000)
  directionLo := (335131433727878319691/100000000000000000000)
  directionHi := (83782858431969579923/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree046.table
  base := (-1754598880367931567718632914852511005711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-217728319541448618020888777922490647500000000000)
      constant := (2553928272231721150900414824808247220498197558884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree046.table
  base := (-7018875368386479711108910907910974646713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-217968953404211778242602343266725960000000000000)
      constant := (2559687656255183061723576138400004831706221076543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335131433727878319691/100000000000000000000)
  centralHi := (83782858431969579923/25000000000000000000)
  directionLo := (67766931182531149327/20000000000000000000)
  directionHi := (84708663978163936659/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree047.table
  base := (-1759693812644468383513698226070853360303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-222456670321326123699203070169173566250000000000)
      constant := (2668183194113675836751351098277048706339114248132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree047.table
  base := (-7039189031849744671644919407389969866313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-222702535355018917838779973890457472500000000000)
      constant := (2674196219625733804808286261360746022708309332143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67766931182531149327/20000000000000000000)
  centralHi := (84708663978163936659/25000000000000000000)
  directionLo := (42812229966738245267/12500000000000000000)
  directionHi := (342497839733905962137/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree048.table
  base := (-7037541380411089476054837641361700197271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-227185021101203629377517362415856485000000000000)
      constant := (2785055493914964601108668446392237352952427920881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree048.table
  base := (-3518949015238395015669689011377828606799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-227436117305826057434957604514188985000000000000)
      constant := (2791327536355692662148468324924064843195727553778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42812229966738245267/12500000000000000000)
  centralHi := (342497839733905962137/100000000000000000000)
  directionLo := (43265282053956244873/12500000000000000000)
  directionHi := (69224451286329991797/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree049.table
  base := (-7014888327527984227910537811412066244787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-231913371881081135055831654662539403750000000000)
      constant := (2904543736435263474446758400294467242518024079957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree049.table
  base := (-1403039120225973679511848795056242147101/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-232169699256633197031135235137920497500000000000)
      constant := (2911080179953344404256057395223330029041496630055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/12500000000000000000)
  centralHi := (69224451286329991797/20000000000000000000)
  directionLo := (349709111365834117489/100000000000000000000)
  directionHi := (34970911136583411749/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree050.table
  base := (-6970980190303408748055406007084104121741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-236641722660958640734145946909222322500000000000)
      constant := (3026646710285764551628729469442178337106791103051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree050.table
  base := (-6971244813113733807504395108115931658517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-236903281207440336627312865761652010000000000000)
      constant := (3033452946626568168705334663231285398303909897987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349709111365834117489/100000000000000000000)
  centralHi := (34970911136583411749/10000000000000000000)
  directionLo := (176629774349644889417/50000000000000000000)
  directionHi := (70651909739857955767/20000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree051.table
  base := (-6905955476835387139893475266789505380753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-241370073440836146412460239155905241250000000000)
      constant := (3151363392987360997999107878986875111036739966983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree051.table
  base := (-3453091638898353096207236719629925324229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-241636863158247476223490496385383522500000000000)
      constant := (3158444820515995605983415211242915122605125331238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176629774349644889417/50000000000000000000)
  centralHi := (70651909739857955767/20000000000000000000)
  directionLo := (178387327830601804641/50000000000000000000)
  directionHi := (356774655661203609283/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree052.table
  base := (-6819931095569553518140964983328503318379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-1456203693613690249057837463920640000000000000)
      constant := (19400549831429007638234451406079173271549886901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree052.table
  base := (-1364025424597985255509207019936306595729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-1457813284668962223785018503012515000000000000)
      constant := (19444112096779819527011423633526115957959807755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178387327830601804641/50000000000000000000)
  centralHi := (356774655661203609283/100000000000000000000)
  directionLo := (360255466436131850609/100000000000000000000)
  directionHi := (36025546643613185061/10000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree053.table
  base := (-3356502861808072885519219573534770678917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-250826775000591157769088823649271078750000000000)
      constant := (3408634567414978391314108798576598860530726064774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree053.table
  base := (-839146793358347979809277200684790727291/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-251104027059861755415845757632846547500000000000)
      constant := (3416282594714712050194895120369211271706854872808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360255466436131850609/100000000000000000000)
  centralHi := (36025546643613185061/10000000000000000000)
  directionLo := (45462870714748411621/12500000000000000000)
  directionHi := (363702965717987292969/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree054.table
  base := (-6585262649803480187070387682715985536617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-255555125780468663447403115895953997500000000000)
      constant := (3541187715852245962794825232090767297264730547087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree054.table
  base := (-6585407648285367496917983206987457492003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-255837609010668895012023388256578060000000000000)
      constant := (3549127161102432647797892077833178447535317065733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45462870714748411621/12500000000000000000)
  centralHi := (363702965717987292969/100000000000000000000)
  directionLo := (367118091963613198639/100000000000000000000)
  directionHi := (4588976149545164983/1250000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree055.table
  base := (-3218386087189305264394753661675104826217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-2151103112068976604344771968120966250000000000)
      constant := (30383073122815078780502667055341010457752154094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree055.table
  base := (-643689681525509018869549871152601088763/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-2153480917036992021555380321324872500000000000)
      constant := (30451141556509542758214549349333508820506581330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367118091963613198639/100000000000000000000)
  centralHi := (4588976149545164983/1250000000000000000)
  directionLo := (370501740376409670057/100000000000000000000)
  directionHi := (185250870188204835029/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree056.table
  base := (-783449204311569975706565546820457178693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-265011827340223674804031700389319835000000000000)
      constant := (3814126525407984241955243848156566529689594962584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree056.table
  base := (-3133850370263833342724691262734983483791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-265304772912283174204378649504041085000000000000)
      constant := (3822665061668843514686219815408833972018249561202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370501740376409670057/100000000000000000000)
  centralHi := (185250870188204835029/50000000000000000000)
  directionLo := (93463691411723151997/25000000000000000000)
  directionHi := (373854765646892607989/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree057.table
  base := (-243111084553043722957878255437142456349/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-747202709473964488870764522537403750000000000)
      constant := (10954325148953285972588598812553118996190482475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree057.table
  base := (-6077869122523814758729465447522684747809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-748028683831275107480765318913497500000000000)
      constant := (10978829900880427347898081970528109088342053759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93463691411723151997/25000000000000000000)
  centralHi := (373854765646892607989/100000000000000000000)
  directionLo := (377177984473958276963/100000000000000000000)
  directionHi := (94294496118489569241/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree058.table
  base := (-1466841221402963638662971599852736387749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-274468528899978686160660284882685672500000000000)
      constant := (4097506095888314817543940425067406625337143489356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree058.table
  base := (-733430487589926535851037736797498839761/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-274771936813897453396733910751504110000000000000)
      constant := (4106665416383683403608384636163403116824900474168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377177984473958276963/100000000000000000000)
  centralHi := (94294496118489569241/25000000000000000000)
  directionLo := (1521888711551706221/400000000000000000)
  directionHi := (380472177887926555251/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree059.table
  base := (-5636392630627640888244795199460246826949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-279196879679856191838974577129368591250000000000)
      constant := (4243110413357842702249706843717162973109932383539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree059.table
  base := (-5636460466945914538549224003356677895993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-279505518764704592992911541375235622500000000000)
      constant := (4252588266900741231943482903142883156746196930623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1521888711551706221/400000000000000000)
  centralHi := (380472177887926555251/100000000000000000000)
  directionLo := (383738093394083755133/100000000000000000000)
  directionHi := (191869046697041877567/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree060.table
  base := (-2692445232626164175310621886488888689837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-283925230459733697517288869376051510000000000000)
      constant := (4391324108858930667833133841370711680486059741014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree060.table
  base := (-2692474343794068904269932003451012586143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-284239100715511732589089171998967135000000000000)
      constant := (4401125925292696935461206272859878235897944414546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383738093394083755133/100000000000000000000)
  centralHi := (191869046697041877567/50000000000000000000)
  directionLo := (386976446953391550009/100000000000000000000)
  directionHi := (38697644695339155001/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree061.table
  base := (-2556441904601864318805942224178558095143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-288653581239611203195603161622734428750000000000)
      constant := (4542146994740959473470358613611794120398405312546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree061.table
  base := (-204517350648045710836143343861414256673/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-288972682666318872185266802622698647500000000000)
      constant := (4552278205504663939864776092328402160253026752575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386976446953391550009/100000000000000000000)
  centralHi := (38697644695339155001/10000000000000000000)
  directionLo := (39018792481523000353/10000000000000000000)
  directionHi := (390187924815230003531/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree062.table
  base := (-4820394117958756564817451486989996590559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-293381932019488708873917453869417347500000000000)
      constant := (4695578912617688996547197951657467253527546902249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree062.table
  base := (-192817478858367085670932810826713634697/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-293706264617126011781444433246430160000000000000)
      constant := (4706044950529396036505652281103746319903831449175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39018792481523000353/10000000000000000000)
  centralHi := (390187924815230003531/100000000000000000000)
  directionLo := (49171648151933056373/12500000000000000000)
  directionHi := (78674637043092890197/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree063.table
  base := (-2253719750478840250972917250583784095541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-298110282799366214552231746116100266250000000000)
      constant := (4851619728803619435774583310387622319535801169702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree063.table
  base := (-450747625146035958887203046779436624349/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-298439846567933151377622063870161672500000000000)
      constant := (4862426027872435532646142547413818427660711149390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49171648151933056373/12500000000000000000)
  centralHi := (78674637043092890197/20000000000000000000)
  directionLo := (99133214987934485889/25000000000000000000)
  directionHi := (396532859951737943557/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree064.table
  base := (-834807048680714202513532500318150908537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-302838633579243720230546038362783185000000000000)
      constant := (5010269330462021341178956148659283148388745031035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree064.table
  base := (-834813350425736331505960911768714174857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-303173428518740290973799694493893185000000000000)
      constant := (5021421325725223535463372629762380262728220318635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99133214987934485889/25000000000000000000)
  centralHi := (396532859951737943557/100000000000000000000)
  directionLo := (79933511169333512569/20000000000000000000)
  directionHi := (199833777923333781423/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree065.table
  base := (-3820194246690559061993905551159512722049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-1819922984373498378158936867511633750000000000)
      constant := (30600755161855946827791331199951400348225677631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree065.table
  base := (-955055313671295867794507743623537084003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-1821934973192588346567913166376477500000000000)
      constant := (30668821004352951468009473570181014075284659828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79933511169333512569/20000000000000000000)
  centralHi := (199833777923333781423/50000000000000000000)
  directionLo := (100694464027135589637/25000000000000000000)
  directionHi := (402777856108542358549/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree066.table
  base := (-3445927400150140548136751624280140010253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-2580953182966931666009707626910322500000000000)
      constant := (44094169620599224799226422289035833406864474723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree066.table
  base := (-3445950544822831592163738736930891621521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-2583806548928550166662437650755010000000000000)
      constant := (44192183638700544749583123480009096358062625311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100694464027135589637/25000000000000000000)
  centralHi := (402777856108542358549/100000000000000000000)
  directionLo := (405864321598164342357/100000000000000000000)
  directionHi := (202932160799082171179/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree067.table
  base := (-1525621947412987895004465083157793249473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-317023685918876237265488915102831941250000000000)
      constant := (5501869967829472598247222160305340763651019721806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree067.table
  base := (-381407965530898854436260715347063898117/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-317374174371161709762332586365087722500000000000)
      constant := (5514091670176974354021621506197628236542056988696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405864321598164342357/100000000000000000000)
  centralHi := (202932160799082171179/50000000000000000000)
  directionLo := (408927492009625941717/100000000000000000000)
  directionHi := (204463746004812970859/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree068.table
  base := (-1318075744158710368574040886598910425753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-321752036698753742943803207349514860000000000000)
      constant := (5670953896297265334557043791058618592493126923966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree068.table
  base := (-2636168473580471312061966484525980687201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-322107756321968849358510216988819235000000000000)
      constant := (5683543042719237385644391926588041042754801057111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408927492009625941717/100000000000000000000)
  centralHi := (204463746004812970859/50000000000000000000)
  directionLo := (1287399646787699647/312500000000000000)
  directionHi := (411967886972063887041/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree069.table
  base := (-68770522760070971186805206980574246809/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-326480387478631248622117499596197778750000000000)
      constant := (5842646261160196536760102998298984231219773371968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree069.table
  base := (-68770977319433620006749688575057542409/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-326841338272775988954687847612550747500000000000)
      constant := (5855608290063289249833857522565910190806845603168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1287399646787699647/312500000000000000)
  centralHi := (411967886972063887041/100000000000000000000)
  directionLo := (414986007078758890391/100000000000000000000)
  directionHi := (51873250884844861299/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree070.table
  base := (-872382570659642537538397967647842687171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-331208738258508754300431791842880697500000000000)
      constant := (6016947021621308154752557628097726720969359039562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree070.table
  base := (-13631074965404719413218271589226416637/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-331574920223583128550865478236282260000000000000)
      constant := (6030287371833529419627862640880116211983026919296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414986007078758890391/100000000000000000000)
  centralHi := (51873250884844861299/12500000000000000000)
  directionLo := (417982334849352505051/100000000000000000000)
  directionHi := (104495583712338126263/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree071.table
  base := (-1268481391826693529156233225223697954881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-335937089038386259978746084089563616250000000000)
      constant := (6193856143246711466641017346293058824248887973591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree071.table
  base := (-1268492053027154435259513730978654602619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-336308502174390268147043108860013772500000000000)
      constant := (6207580253958687220793599912206809055091956908909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417982334849352505051/100000000000000000000)
  centralHi := (104495583712338126263/25000000000000000000)
  directionLo := (420957335630418441291/100000000000000000000)
  directionHi := (105239333907604610323/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree072.table
  base := (-192952354206292376364236395312811360011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-340665439818263765657060376336246535000000000000)
      constant := (6373373596973264752577971265603537944800751028084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree072.table
  base := (-771818541310813193196366642628859253993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-341042084125197407743220739483745285000000000000)
      constant := (6387486907687571676313727644544587312018550068623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420957335630418441291/100000000000000000000)
  centralHi := (105239333907604610323/25000000000000000000)
  directionLo := (2119557292195738673/500000000000000000)
  directionHi := (423911458439147734601/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree073.table
  base := (-254752539218192454701413421606562636091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-345393790598141271335374668582929453750000000000)
      constant := (6555499358270998788848514921281046030972239125901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree073.table
  base := (-127380173493026832424693413988863761697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-345775666076004547339398370107476797500000000000)
      constant := (6570007308758480198510945253789148179623305909934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2119557292195738673/500000000000000000)
  centralHi := (423911458439147734601/100000000000000000000)
  directionLo := (426845136754478901061/100000000000000000000)
  directionHi := (213422568377239450531/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree074.table
  base := (282686436401214059071586943155610509709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-350122141378018777013688960829612372500000000000)
      constant := (6740233406436158266723816867149976353100757202101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree074.table
  base := (141339878297294121676049529368823213549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-350509248026811686935576000731208310000000000000)
      constant := (6755141436698277538948295778368841201700369447722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426845136754478901061/100000000000000000000)
  centralHi := (213422568377239450531/50000000000000000000)
  directionLo := (42975878925961981141/10000000000000000000)
  directionHi := (429758789259619811411/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree075.table
  base := (13132892858096329120758622576617545953/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-354850492157896282692003253076295291250000000000)
      constant := (6927575723994490432114825059250353861162382192288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree075.table
  base := (840499429163701978663165165904644591913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-355242829977618826531753631354939822500000000000)
      constant := (6942889274230901389125876981348661238609620446257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42975878925961981141/10000000000000000000)
  centralHi := (429758789259619811411/100000000000000000000)
  directionLo := (43265282053956244873/10000000000000000000)
  directionHi := (432652820539562448731/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree076.table
  base := (709350791234544701341865783783777248919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-996063276835938471939937798678610000000000000)
      constant := (19716139324647059814088062484893152046926289262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree076.table
  base := (1418696695922502470807925946282895115919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-997164575979019296753272193846735000000000000)
      constant := (19759697525701416511254961277188548922225427631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/10000000000000000000)
  centralHi := (432652820539562448731/100000000000000000000)
  directionLo := (435527621736880596723/100000000000000000000)
  directionHi := (108881905434220149181/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree077.table
  base := (2017274068854649048831432871649561428489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-3010803253864886727674643285699678750000000000)
      constant := (60413926533865943503963096864772932429128185401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree077.table
  base := (252158736310070690430966773965194795787/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-3014132180820108311769494980185147500000000000)
      constant := (60547322496188140769377376278412272273119352664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435527621736880596723/100000000000000000000)
  centralHi := (108881905434220149181/25000000000000000000)
  directionLo := (438383571168819995259/100000000000000000000)
  directionHi := (21919178558440999763/5000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree078.table
  base := (2636221178933198498858653086199701206809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-2183642275133306507260036271102627500000000000)
      constant := (44409776075084638217065983251180208367164623929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree078.table
  base := (263621760670379569408145811933146345187/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-2186056661716214469350807829740440000000000000)
      constant := (44507780530368966675915406921864503280041133470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438383571168819995259/100000000000000000000)
  centralHi := (21919178558440999763/5000000000000000000)
  directionLo := (55152629363554653581/12500000000000000000)
  directionHi := (441221034908437228649/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree079.table
  base := (3275541711594321381386910577554711619507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-373763895277406305405260422063026966250000000000)
      constant := (7703027425605458684519066899377651461630472310123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree079.table
  base := (1637769329039951309280974701535470596359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-374177157780847384916464153849865872500000000000)
      constant := (7720017460800043038906188083347673869167160427902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55152629363554653581/12500000000000000000)
  centralHi := (441221034908437228649/100000000000000000000)
  directionLo := (444040367332314620563/100000000000000000000)
  directionHi := (111010091833078655141/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree080.table
  base := (3935234653130373826952677918016155433003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-378492246057283811083574714309709885000000000000)
      constant := (7903410909862963594459597768696902637844261683267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree080.table
  base := (787046408685555080343388447545980134319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-378910739731654524512641784473597385000000000000)
      constant := (7920833668151019979377084133839885834718874061955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444040367332314620563/100000000000000000000)
  centralHi := (111010091833078655141/25000000000000000000)
  directionLo := (223420955818585546461/50000000000000000000)
  directionHi := (446841911637171092923/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree081.table
  base := (4615299148008299902823838826980394892103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-383220596837161316761889006556392803750000000000)
      constant := (8106402603146197427168337281865443715059587243167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree081.table
  base := (4615296917960363653659899341331403222967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-383644321682461664108819415097328897500000000000)
      constant := (8124263525448992997616764803154365093805579238063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223420955818585546461/50000000000000000000)
  centralHi := (446841911637171092923/100000000000000000000)
  directionLo := (449626000327501008201/100000000000000000000)
  directionHi := (224813000163750504101/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree082.table
  base := (1063146894839914876454687241520955654247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-387948947617038822440203298803075722500000000000)
      constant := (8312002500125081348882841862895200619242272909915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree082.table
  base := (265786628443264473303678800531706350873/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-388377903633268803704997045721060410000000000000)
      constant := (8330307027431917679604398350657005620205194273940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449626000327501008201/100000000000000000000)
  centralHi := (224813000163750504101/50000000000000000000)
  directionLo := (113098238919050606959/25000000000000000000)
  directionHi := (452392955676202427837/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree083.table
  base := (6036540022357454979266124680526028815201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-392677298396916328118517591049758641250000000000)
      constant := (8520210596301363476187535135049974878053815834889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree083.table
  base := (6036538394697892483228621969111023955057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-393111485584075943301174676344791922500000000000)
      constant := (8538964169659876014019219052694310133936112774073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113098238919050606959/25000000000000000000)
  centralHi := (452392955676202427837/100000000000000000000)
  directionLo := (455143090160001190157/100000000000000000000)
  directionHi := (227571545080000595079/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree084.table
  base := (6777715278241573579745111391092646770829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-397405649176793833796831883296441560000000000000)
      constant := (8731026887878875644271687702422165056332822281781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree084.table
  base := (3388856943995759252750607049898962457093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-397845067534883082897352306968523435000000000000)
      constant := (8750234948386703995027380080496591728731838414554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455143090160001190157/100000000000000000000)
  centralHi := (227571545080000595079/50000000000000000000)
  directionLo := (457876706871336150901/100000000000000000000)
  directionHi := (228938353435668075451/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree085.table
  base := (7539259807883457554619463289890040790203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-402133999956671339475146175543124478750000000000)
      constant := (8944451371654023964993286308147951242850346374067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree085.table
  base := (7539258620582780762311702242497178422573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-402578649485690222493529937592254947500000000000)
      constant := (8964119360451661394947039874992407083833063494997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457876706871336150901/100000000000000000000)
  centralHi := (228938353435668075451/50000000000000000000)
  directionLo := (92118819981648485657/20000000000000000000)
  directionHi := (230297049954121214143/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree086.table
  base := (1664234649013108708572136907594481747819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-406862350736548845153460467789807397500000000000)
      constant := (9160484044923357792258079464408105860075127069455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree086.table
  base := (4160586115613967828381993962614477319557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-407312231436497362089707568215986460000000000000)
      constant := (9180617403188014747852731313508837089147902429146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92118819981648485657/20000000000000000000)
  centralHi := (230297049954121214143/50000000000000000000)
  directionLo := (57911944342956537533/12500000000000000000)
  directionHi := (92659110948730460053/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree087.table
  base := (4561727640376451192277836153144511576919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-411590701516426350831774760036490316250000000000)
      constant := (9379124905405553774898893413852424652355630307582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree087.table
  base := (2280863603788171506080511456513366268479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-412045813387304501685885198839717972500000000000)
      constant := (9399729074345893067163401813413068573402789490524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57911944342956537533/12500000000000000000)
  centralHi := (92659110948730460053/20000000000000000000)
  directionLo := (232990674287713199857/50000000000000000000)
  directionHi := (93196269715085279943/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree088.table
  base := (2486526413543288899096812925250477556733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-3440653324762841789339578944489035000000000000)
      constant := (79341933480789809968679303770132480541034894388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree088.table
  base := (310815778601048932263498307736770843011/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-3444457812711666456876552309615285000000000000)
      constant := (79516151834935438368911250953936859875560259168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232990674287713199857/50000000000000000000)
  centralHi := (93196269715085279943/20000000000000000000)
  directionLo := (58581468832291256309/12500000000000000000)
  directionHi := (468651750658330050473/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree089.table
  base := (431564965811502074892780277539868650429/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-421047403076181362188403344529856153750000000000)
      constant := (9824231180609051840601963123897776438730356654525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree089.table
  base := (21072506864367545899903749256225490017/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-421512977288918780878240460087180997500000000000)
      constant := (9845793294630618330250367526512675309362292022656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58581468832291256309/12500000000000000000)
  centralHi := (468651750658330050473/100000000000000000000)
  directionLo := (94261404523816019497/20000000000000000000)
  directionHi := (235653511309540048743/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree090.table
  base := (5826255284218127370587577582995753200623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-425775753856058867866717636776539072500000000000)
      constant := (10050696592335450841518518880190253391466817682894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree090.table
  base := (2913127507533841899068428644935052391361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-426246559239725920474418090710912510000000000000)
      constant := (10072745840805371108801022414051559552015758932516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94261404523816019497/20000000000000000000)
  centralHi := (235653511309540048743/50000000000000000000)
  directionLo := (94789483751101123163/20000000000000000000)
  directionHi := (59243427344438201977/12500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree091.table
  base := (12536264766974724544000016440706244403407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-2547361565893114636361135674693621250000000000)
      constant := (60827042515966864354043985927833395672722721167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree091.table
  base := (12536264307615817042853220420914594335741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-2550178350239840592133702493104402500000000000)
      constant := (60960426091195158627954484339649553363929502621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94789483751101123163/20000000000000000000)
  centralHi := (59243427344438201977/12500000000000000000)
  directionLo := (476573186320790727413/100000000000000000000)
  directionHi := (238286593160395363707/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree092.table
  base := (420012081523332313920382353049180943471/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-435232455415813879223346221269904910000000000000)
      constant := (10511451958222309773982289826270285851382820509408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree092.table
  base := (13440386216800177372956014836061662164271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-435713723141340199666773351958375535000000000000)
      constant := (10534491799489321969976345987035852419584581142119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476573186320790727413/100000000000000000000)
  centralHi := (238286593160395363707/50000000000000000000)
  directionLo := (119796141448424694203/25000000000000000000)
  directionHi := (479184565793698776813/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree093.table
  base := (1436487598226285999988058580801657057419/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-439960806195691384901660513516587828750000000000)
      constant := (10745741910584157305633721280825712050851889182910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree093.table
  base := (14364875647875362828236161778050696398727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-440447305092147339262950982582107047500000000000)
      constant := (10769285210226741621924394622268566110296132200703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119796141448424694203/25000000000000000000)
  centralHi := (479184565793698776813/100000000000000000000)
  directionLo := (96356358227122749553/20000000000000000000)
  directionHi := (240890895567806873883/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree094.table
  base := (7654866396738218644991766198133244890669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-444689156975568890579974805763270747500000000000)
      constant := (10982640041589679604111912610013136140752177655082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree094.table
  base := (3827433127057027871861287229920016288651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-445180887042954478859128613205838560000000000000)
      constant := (11006692240940561421885486249981916023122085487756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96356358227122749553/20000000000000000000)
  centralHi := (240890895567806873883/50000000000000000000)
  directionLo := (121091272508794132779/25000000000000000000)
  directionHi := (484365090035176531117/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree095.table
  base := (16274956963060533987712138129926895472113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-1244923844197912455009111074819816250000000000)
      constant := (31086277979648972121983282451640495983946738737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree095.table
  base := (8137478359878889758618689833572836540111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-1246300468126763486025779068779972500000000000)
      constant := (31154329338100375252422610826488486087567459678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121091272508794132779/25000000000000000000)
  centralHi := (484365090035176531117/100000000000000000000)
  directionLo := (19477387365649600801/4000000000000000000)
  directionHi := (243467342070620010013/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree096.table
  base := (1078784276506937474528306188434345750227/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-454145858535323901936603390256636585000000000000)
      constant := (11464260837281062907940954904827041085759159747248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree096.table
  base := (8630274108304371312985137401075707206933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-454648050944568758051483874453301585000000000000)
      constant := (11489347160081611674970155921430836192679041646074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19477387365649600801/4000000000000000000)
  centralHi := (243467342070620010013/50000000000000000000)
  directionLo := (244745394642408799093/50000000000000000000)
  directionHi := (489490789284817598187/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree097.table
  base := (9133253560103636184360848564874851444803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-458874209315201407614917682503319503750000000000)
      constant := (11708983501056529911665544212783968996915566166934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree097.table
  base := (9133253471628446320515402301451924023901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-459381632895375897647661505077033097500000000000)
      constant := (11734595047612806140246409741221469746450100618378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244745394642408799093/50000000000000000000)
  centralHi := (489490789284817598187/100000000000000000000)
  directionLo := (98406723138130805363/20000000000000000000)
  directionHi := (7688025245166469169/1562500000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree098.table
  base := (19292833003775757603075465811096349431943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-463602560095078913293231974750002422500000000000)
      constant := (11956314341628487436985166674372098080800452668927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree098.table
  base := (19292832852894944860216498220677541572097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-464115214846183037243839135700764610000000000000)
      constant := (11982456553302283320433326831909047460311419970633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98406723138130805363/20000000000000000000)
  centralHi := (7688025245166469169/1562500000000000000)
  directionLo := (494563368179005690367/100000000000000000000)
  directionHi := (965944078474620489/195312500000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree099.table
  base := (4067905206941700846264643678629156905959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-3870503395660796851004514603278391250000000000)
      constant := (100878126931412024954845617463027743629315763155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree099.table
  base := (635610184564684463605834512825559453247/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-3874783444603224601983609639045422500000000000)
      constant := (101098608899659484995322719185823268782610679136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494563368179005690367/100000000000000000000)
  centralHi := (965944078474620489/195312500000000000)
  directionLo := (248540123179089162537/50000000000000000000)
  directionHi := (19883209854327133003/4000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree100.table
  base := (10703293089598681881258447019199207115027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-473059261654833924649860559243368260000000000000)
      constant := (12458800552024057898233609049266909151930125102806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree100.table
  base := (10703293034766655402771229739287502164581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-473582378747797316436194396948227635000000000000)
      constant := (12486020418036906172708319231054619650133259179418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248540123179089162537/50000000000000000000)
  centralHi := (19883209854327133003/4000000000000000000)
  directionLo := (124896111202083613389/25000000000000000000)
  directionHi := (499584444808334453557/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree101.table
  base := (22494013408750024696963720576133647921897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-477787612434711430328174851490051178750000000000)
      constant := (12713955921387763293770579166272772005127546202833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree101.table
  base := (11247006657635535232429280833873943223259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-478315960698604456032372027571959147500000000000)
      constant := (12741722776629806218307786602802969542778839616102) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124896111202083613389/25000000000000000000)
  centralHi := (499584444808334453557/100000000000000000000)
  directionLo := (251038076628524767047/50000000000000000000)
  directionHi := (100415230651409906819/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree102.table
  base := (23601807699359556600692546217082793350031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-482515963214588936006489143736734097500000000000)
      constant := (12971719466614749909066846398103054807597286994759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree102.table
  base := (23601807619684785647024679099772356535953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-483049542649411595628549658195690660000000000000)
      constant := (13000038752463292360475489465185519976313136745817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251038076628524767047/50000000000000000000)
  centralHi := (100415230651409906819/20000000000000000000)
  directionLo := (31534722296691567441/6250000000000000000)
  directionHi := (504555556747065079057/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree103.table
  base := (6182492257700880414868232815141680271509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-487244313994466441684803435983417016250000000000)
      constant := (13232091187555733908380796172378210865456231909204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree103.table
  base := (24729968962900975635309928189698199752949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-487783124600218735224727288819422172500000000000)
      constant := (13260968345390656795820736646529529404184797530461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31534722296691567441/6250000000000000000)
  centralHi := (504555556747065079057/100000000000000000000)
  directionLo := (3961115904661394523/781250000000000000)
  directionHi := (101404567159331699789/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree104.table
  base := (12939248693026222672569133247154338883021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-2911080856652922765462235078284615000000000000)
      constant := (79852491621804746716699819958964457353498480602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree104.table
  base := (12939248664094095792987062714043229127433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-2914300038763466714916597156468365000000000000)
      constant := (80026695593422405206391071120070929583030801746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3961115904661394523/781250000000000000)
  centralHi := (101404567159331699789/20000000000000000000)
  directionLo := (509478166553023000783/100000000000000000000)
  directionHi := (31842385409563937549/6250000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree105.table
  base := (13523696375385294681819496261269618935517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-496701015554221453041432020476782853750000000000)
      constant := (13760659156096727073323884582293045966792081010026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree105.table
  base := (27047392701465187663141274303846029356763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-497250288501833014417082550066885197500000000000)
      constant := (13790668382052532402662236584264329055226987217907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509478166553023000783/100000000000000000000)
  centralHi := (31842385409563937549/6250000000000000000)
  directionLo := (511921720939026343277/100000000000000000000)
  directionHi := (255960860469513171639/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree106.table
  base := (3529581889111828764992812575281884001091/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-501429366334098958719746312723465772500000000000)
      constant := (14028855403501856014571310524419340182738588872792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree106.table
  base := (28236655070885928953419445141837411153303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-501983870452640154013260180690616710000000000000)
      constant := (14059438825595646080139406824702934380788275389967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511921720939026343277/100000000000000000000)
  centralHi := (255960860469513171639/50000000000000000000)
  directionLo := (514353666793694472803/100000000000000000000)
  directionHi := (128588416698423618201/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree107.table
  base := (29446284462278091171652271981510946017831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-506157717113976464398060604970148691250000000000)
      constant := (14299659826225486826730372924726847298876261528959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree107.table
  base := (7361571106622359507776329649563817676153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-506717452403447293609437811314348222500000000000)
      constant := (14330822885844194690428068949616410509779288494468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514353666793694472803/100000000000000000000)
  centralHi := (128588416698423618201/25000000000000000000)
  directionLo := (516774168006744893939/100000000000000000000)
  directionHi := (25838708400337244697/5000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree108.table
  base := (30676280790391273241285069692951039993911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-510886067893853970076374897216831610000000000000)
      constant := (14573072424204652510591454831914456558002610460079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree108.table
  base := (30676280759904355291926202541786344825843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-511451034354254433205615441938079735000000000000)
      constant := (14604820562736380111878477165421803246489062526027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516774168006744893939/100000000000000000000)
  centralHi := (25838708400337244697/5000000000000000000)
  directionLo := (129795846161868734619/25000000000000000000)
  directionHi := (519183384647474938477/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree109.table
  base := (6385328818013604983751525910686311572873/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-515614418673731475754689189463514528750000000000)
      constant := (14849093197386451898657846092371688157711829858485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree109.table
  base := (31926644064099668968197459257018212840331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-516184616305061572801793072561811247500000000000)
      constant := (14881431856220298789861536152571181429777016231459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129795846161868734619/25000000000000000000)
  centralHi := (519183384647474938477/100000000000000000000)
  directionLo := (521581473088291771413/100000000000000000000)
  directionHi := (260790736544145885707/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree110.table
  base := (4149671794411505912271537590294034086197/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-4300353466558751912669450262067747500000000000)
      constant := (125022497072119604437649649774399226523268342184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree110.table
  base := (33197374333174404737880354426798611450121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-4305109076494782747090666968475560000000000000)
      constant := (125294684018614786832605300106512172110960432089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521581473088291771413/100000000000000000000)
  centralHi := (260790736544145885707/50000000000000000000)
  directionLo := (52396858612315390517/10000000000000000000)
  directionHi := (523968586123153905171/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree111.table
  base := (17244235790508282678403353546904041454491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-525071120233486487111317773956880366250000000000)
      constant := (15408959269187457483104025820201046427539421523398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree111.table
  base := (34488471562180190573415883340919867852929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-525651780206675851994148333809274272500000000000)
      constant := (15442495292796122039817041620850005184327310788681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52396858612315390517/10000000000000000000)
  centralHi := (523968586123153905171/100000000000000000000)
  directionLo := (526344873081178087063/100000000000000000000)
  directionHi := (65793109135147260883/12500000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree112.table
  base := (35799935763012160733396655496311736107671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-529799471013363992789632066203563285000000000000)
      constant := (15692804567738185994342014258362797052691340904719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree112.table
  base := (17899967873485781228735182118263355062177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-530385362157482991590325964433005785000000000000)
      constant := (15726947435820895104754682294986203995015182295506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526344873081178087063/100000000000000000000)
  centralHi := (65793109135147260883/12500000000000000000)
  directionLo := (33044404995978161963/6250000000000000000)
  directionHi := (528710479935650591409/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree113.table
  base := (37131766897738372411174126411399599688537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-534527821793241498467946358450246203750000000000)
      constant := (15979258041352521672342760924748522605676089913793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree113.table
  base := (18565883442039839129983068077080209465769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-535118944108290131186503595056737297500000000000)
      constant := (16014013195301101100226980465182019599548648422882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33044404995978161963/6250000000000000000)
  centralHi := (528710479935650591409/100000000000000000000)
  directionLo := (531065549408668105079/100000000000000000000)
  directionHi := (13276638735216702627/2500000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree114.table
  base := (2405247811389709815668910503242072143741/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-1493784411559886438078284350961022500000000000)
      constant := (45064597479248240138915479180642699601027755344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree114.table
  base := (38483964970605783578553697327397416390523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-1495436360274507675298285943713210000000000000)
      constant := (45162583299765487986832826316598492892769804827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531065549408668105079/100000000000000000000)
  centralHi := (13276638735216702627/2500000000000000000)
  directionLo := (133352555267905117407/25000000000000000000)
  directionHi := (533410221071620469629/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree115.table
  base := (39856530014032479092513208177703907019231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-543984523352996509824574942943612041250000000000)
      constant := (16559989513688226596172632167356653206287125453559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree115.table
  base := (39856530004131344232765867695597201879529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-544586108009904410378858856304200322500000000000)
      constant := (16595985563545761459243941015529639426644400356081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133352555267905117407/25000000000000000000)
  centralHi := (533410221071620469629/100000000000000000000)
  directionLo := (267872315720857732969/50000000000000000000)
  directionHi := (535744631441715465939/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree116.table
  base := (41249461991071188925072715031258123986127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-548712874132874015502889235190294960000000000000)
      constant := (16854267512376160993971938992681059903863624279303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree116.table
  base := (41249461982642241859752519611667806202999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-549319689960711549975036486927931835000000000000)
      constant := (16890892172277493587207758674942576568825290684911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267872315720857732969/50000000000000000000)
  centralHi := (535744631441715465939/100000000000000000000)
  directionLo := (538068914074734536271/100000000000000000000)
  directionHi := (33629307129670908517/6250000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree117.table
  base := (42662760911639959456046387551894199009753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-3274800147412730894563334481875608750000000000)
      constant := (101486116485560847563460843071995171092882520793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree117.table
  base := (42662760904464835601743661882879362203403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-3278421727287092837699491819832327500000000000)
      constant := (101706582233125340718177567230869345139156846443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538068914074734536271/100000000000000000000)
  centralHi := (33629307129670908517/6250000000000000000)
  directionLo := (270191599827098887957/50000000000000000000)
  directionHi := (108076639930839555183/20000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree118.table
  base := (22048213387159699603467199846107525047913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-558169575692629026859517819683660797500000000000)
      constant := (17450648034728615254711335324448621761165596060514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree118.table
  base := (44096426768212035944873912925544634117841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-558786853862325829167391748175394860000000000000)
      constant := (17488546238897588823494370595882927583155338749849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270191599827098887957/50000000000000000000)
  centralHi := (108076639930839555183/20000000000000000000)
  directionLo := (135671904019276659939/25000000000000000000)
  directionHi := (542687616077106639757/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree119.table
  base := (45550459577935953594226603753508214826763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-562897926472506532537832111930343716250000000000)
      constant := (17752750558373993759049467685810332860293221547907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree119.table
  base := (711725930824028535549008926620182037907/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-563520435813132968763569378799126372500000000000)
      constant := (17791293696767252316934767759943828437470724254272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135671904019276659939/25000000000000000000)
  centralHi := (542687616077106639757/100000000000000000000)
  directionLo := (5449822885364235493/1000000000000000000)
  directionHi := (544982288536423549301/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree120.table
  base := (47024859321522853822751112085802997528519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-567626277252384038216146404177026635000000000000)
      constant := (18057461256988781977950897918322232689222307296191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree120.table
  base := (47024859317098912022400574452371883706367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-568254017763940108359747009422857885000000000000)
      constant := (18096654771000209577223276108680603581618051060663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5449822885364235493/1000000000000000000)
  centralHi := (544982288536423549301/100000000000000000000)
  directionLo := (547267339600438908281/100000000000000000000)
  directionHi := (273633669800219454141/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree121.table
  base := (48519626004287181938325983985909866481799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-4730203537456706974334385920857103750000000000)
      constant := (151775042401381210913290553830749202817625575191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree121.table
  base := (48519626000522383424481599437184652494979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-4735434708386340892197724297905697500000000000)
      constant := (152104375715626073683524645750303851432816173811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547267339600438908281/100000000000000000000)
  centralHi := (273633669800219454141/50000000000000000000)
  directionLo := (17173215290286496841/3125000000000000000)
  directionHi := (549542889289167898913/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree122.table
  base := (50034759625582097093240103857864741775487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-577082978812139049572774988670392472500000000000)
      constant := (18674707179104252350014606069786900536717413052343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree122.table
  base := (12508689905594612978842007536847804276129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-577721181665554387552102270670320910000000000000)
      constant := (18715217768534239177138905716099008530608859413924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17173215290286496841/3125000000000000000)
  centralHi := (549542889289167898913/100000000000000000000)
  directionLo := (551809055147911797993/100000000000000000000)
  directionHi := (275904527573955898997/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree123.table
  base := (10314052036976683411164971483550575679073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-581811329592016555251089280917075391250000000000)
      constant := (18987242402596289906583848757970443760469199117485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree123.table
  base := (51570260182157466950311817535192889792309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-582454763616361527148279901294052422500000000000)
      constant := (19028419691826900075840318268970115936332766553501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551809055147911797993/100000000000000000000)
  centralHi := (275904527573955898997/50000000000000000000)
  directionLo := (277032976159055693791/50000000000000000000)
  directionHi := (554065952318111387583/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree124.table
  base := (3320382980110617171098362080675271324853/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-586539680371894060929403573163758310000000000000)
      constant := (19302385801040129359075759576948559196432404126672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree124.table
  base := (53126127679450543966484773828541272137251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-587188345567168666744457531917783935000000000000)
      constant := (19344235231465719189577196020558115251090407097339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277032976159055693791/50000000000000000000)
  centralHi := (554065952318111387583/100000000000000000000)
  directionLo := (278156846802806653223/50000000000000000000)
  directionHi := (556313693605613306447/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree125.table
  base := (54702362115906475641563620015898264949819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-591268031151771566607717865410441228750000000000)
      constant := (19620137374433297748299540562982312577703581891891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree125.table
  base := (5470236211393323872007095884569288525353/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-591921927517975806340635162541515447500000000000)
      constant := (19662664387448301442066152000822699938577096024170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278156846802806653223/50000000000000000000)
  centralHi := (556313693605613306447/100000000000000000000)
  directionLo := (69819048693307983269/12500000000000000000)
  directionHi := (558552389546463866153/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree126.table
  base := (14074740871757617928217845402838384964263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-595996381931649072286032157657124147500000000000)
      constant := (19940497122773855444729173566871851582158555141628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree126.table
  base := (28149481742675895729546714403178864735297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-596655509468782945936812793165246960000000000000)
      constant := (19983707159772773556233474484829772775414847790866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69819048693307983269/12500000000000000000)
  centralHi := (558552389546463866153/100000000000000000000)
  directionLo := (280391074235169455991/50000000000000000000)
  directionHi := (560782148470338911983/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree127.table
  base := (11583186358987908535368397969752032596569/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-600724732711526577964346449903807066250000000000)
      constant := (20263465046060308902090650283012201239629804763205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree127.table
  base := (5791593179351153883454188250958384758897/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-601389091419590085532990423788978472500000000000)
      constant := (20307363548437698509911731367197099528832961958330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280391074235169455991/50000000000000000000)
  centralHi := (560782148470338911983/100000000000000000000)
  directionLo := (35187692285107044887/6250000000000000000)
  directionHi := (563003076561712718193/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree128.table
  base := (29776633519740919881709591474894405029547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-605453083491404083642660742150489985000000000000)
      constant := (20589041144291537159248874851948436207060327167366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree128.table
  base := (29776633519133577135586848368666815623943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-606122673370397225129168054412709985000000000000)
      constant := (20633633553442003489388416406735660168565075513854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35187692285107044887/6250000000000000000)
  centralHi := (563003076561712718193/100000000000000000000)
  directionLo := (282607638959431823067/50000000000000000000)
  directionHi := (113043055583772729227/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree129.table
  base := (61210969220547600574484264021018330381499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-610181434271281589320975034397172903750000000000)
      constant := (20917225417466729940412081620649298035468567071411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree129.table
  base := (61210969219514430528632326457954472706309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-610856255321204364725345685036441497500000000000)
      constant := (20962517174784919227540773196289287327184793899501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282607638959431823067/50000000000000000000)
  centralHi := (113043055583772729227/20000000000000000000)
  directionLo := (567418854610809340289/100000000000000000000)
  directionHi := (56741885461080934029/10000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree130.table
  base := (62889038338062089308606356065646122743009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-3638519438172539023664433885466602500000000000)
      constant := (125727916364410269462974091880333356256287376129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree130.table
  base := (62889038337183362914842414171271847317841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-3642543415810718960482386483196290000000000000)
      constant := (126000085280863484872789845278608728687690612721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567418854610809340289/100000000000000000000)
  centralHi := (56741885461080934029/10000000000000000000)
  directionLo := (8900217292691555803/1562500000000000000)
  directionHi := (569613906732259571393/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree131.table
  base := (64587474391979654924061622745020279605641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-619638135831036600677603618890538741250000000000)
      constant := (21581418488647016955687546500056191201127164264049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree131.table
  base := (64587474391232329359464874047760047042549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-620323419222818643917700946283904522500000000000)
      constant := (21628125266484725379442940982350226027131033504861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8900217292691555803/1562500000000000000)
  centralHi := (569613906732259571393/100000000000000000000)
  directionLo := (4467191659817737801/781250000000000000)
  directionHi := (571800532456670438529/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree132.table
  base := (66306277382278732202356790789822661640617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-5160053608354662035999321579646460000000000000)
      constant := (181135762699600123912269708663747376389032402553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree132.table
  base := (4144142336352699712888060570840487111863/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-5165760340277899037304781627335835000000000000)
      constant := (181527683775546898059461485595169711451322396272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4467191659817737801/781250000000000000)
  centralHi := (571800532456670438529/100000000000000000000)
  directionLo := (573978828087479496139/100000000000000000000)
  directionHi := (28698941404373974807/5000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree133.table
  base := (68045447308957638004253055640549297266363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-1742644978921860421147457627102228750000000000)
      constant := (61651092131853510324792869875446529415737356987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree133.table
  base := (34022723654208599529700896533521458599129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-1744572252422251864570792818646447500000000000)
      constant := (61784453804806886259876191596767527332537177842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573978828087479496139/100000000000000000000)
  centralHi := (28698941404373974807/5000000000000000000)
  directionLo := (576148888107597461049/100000000000000000000)
  directionHi := (11522977762151949221/2000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree134.table
  base := (3490249208601551903815704273140278232331/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-633823188170669117712546495630587497500000000000)
      constant := (22597269407489631921130704772789450569635352389180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree134.table
  base := (69804984171571493099111362477504106319281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-634524165075240062706233838155099060000000000000)
      constant := (22646139526567185826653396735411305891339394758009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576148888107597461049/100000000000000000000)
  centralHi := (11522977762151949221/2000000000000000000)
  directionLo := (72288850653403557989/12500000000000000000)
  directionHi := (578310805227228463913/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree135.table
  base := (35792443985763489616653743920171527721821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-638551538950546623390860787877270416250000000000)
      constant := (22941102730323366119108851985073522098277837228138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree135.table
  base := (71584887971136241615747185778703996205439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-639257747026047202302411468778830572500000000000)
      constant := (22990704845937096999709121501507677285112962982071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72288850653403557989/12500000000000000000)
  centralHi := (578310805227228463913/100000000000000000000)
  directionLo := (290232335215043662507/50000000000000000000)
  directionHi := (116092934086017465003/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree136.table
  base := (14677031741496879634334557284641627008273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-643279889730424129069175080123953335000000000000)
      constant := (23287544228100607255343150208590658828399375111485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree136.table
  base := (73385158707152183662529574280588957354491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-643991328976854341898589099402562085000000000000)
      constant := (23337883781645320198299127539419922240608057111699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290232335215043662507/50000000000000000000)
  centralHi := (116092934086017465003/20000000000000000000)
  directionLo := (291305286509039521539/50000000000000000000)
  directionHi := (582610573018079043079/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree137.table
  base := (601646371039608256283944607997794578107/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-648008240510301634747489372370636253750000000000)
      constant := (23636593900821707729679826672463701136748853190375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree137.table
  base := (75205796379668590549278417881278859563147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-648724910927661481494766730026293597500000000000)
      constant := (23687676333692219147617651850346162569332402274083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291305286509039521539/50000000000000000000)
  centralHi := (582610573018079043079/100000000000000000000)
  directionLo := (584748600654502575639/100000000000000000000)
  directionHi := (14618715016362564391/2500000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree138.table
  base := (77046800988981667558848191131817531737043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-652736591290179140425803664617319172500000000000)
      constant := (23988251748487071982665878048534062136511926022827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree138.table
  base := (77046800988741554797502300538617790707869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-653458492878468621090944360650025110000000000000)
      constant := (24040082502078207927650705215327175576113861958341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584748600654502575639/100000000000000000000)
  centralHi := (14618715016362564391/2500000000000000000)
  directionLo := (293439419702919024741/50000000000000000000)
  directionHi := (586878839405838049483/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree139.table
  base := (39454086267318337742298390818219297415897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-657464942070056646104117956864002091250000000000)
      constant := (24342517771097145676498083004170306573481680837666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree139.table
  base := (39454086267216279238575922717760077618467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-658192074829275760687121991273756622500000000000)
      constant := (24395102286803740404510567360304698673971612875126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293439419702919024741/50000000000000000000)
  centralHi := (586878839405838049483/100000000000000000000)
  directionLo := (73625171722771719869/12500000000000000000)
  directionHi := (589001373782173758953/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree140.table
  base := (80789911016980785294407283462818670271953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-662193292849934151782432249110685010000000000000)
      constant := (24699391968652406649971041802040458342934211249817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree140.table
  base := (10098738877100909603765459002690617657171/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-662925656780082900283299621897488135000000000000)
      constant := (24752735687869301398678015658854359682081662481752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73625171722771719869/12500000000000000000)
  centralHi := (589001373782173758953/100000000000000000000)
  directionLo := (295558143388163339591/50000000000000000000)
  directionHi := (591116286776326679183/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree141.table
  base := (82692016436082062318678251368653790475021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-666921643629811657460746541357367928750000000000)
      constant := (25058874341153357367411570978837202991122394798869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree141.table
  base := (41346008217967289995678213812203762149473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-667659238730890039879477252521219647500000000000)
      constant := (25112982705275399315618609215089408594613231978194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295558143388163339591/50000000000000000000)
  centralHi := (591116286776326679183/100000000000000000000)
  directionLo := (593223659901707731087/100000000000000000000)
  directionHi := (37076478743856733193/6250000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree142.table
  base := (42307244396005527615400670981577378433577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-671649994409689163139060833604050847500000000000)
      constant := (25420964888600518625405479675507172873935442004706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree142.table
  base := (16922897758377140288976991338790958414173/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-672392820681697179475654883144951160000000000000)
      constant := (25475843339022560007251273329839328247668619736985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593223659901707731087/100000000000000000000)
  centralHi := (37076478743856733193/6250000000000000000)
  directionLo := (59532357322898067709/10000000000000000000)
  directionHi := (595323573228980677091/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree143.table
  base := (86557328084840086939317532169705620738569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (222416218546672871392289038150000000000000)
      linear := (-33076353131672290518723415612046250000000000)
      constant := (1260974307349720001863189214330565565024123409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree143.table
  base := (86557328084733546768063108161512596889831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (64258)
      previous := (32129)
      next := (32129)
      square := (222416218546672871392289038150000000000000)
      linear := (-33112934746564835398886621045952500000000000)
      constant := (1263695906357832738473110201007769016227228991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59532357322898067709/10000000000000000000)
  centralHi := (595323573228980677091/100000000000000000000)
  directionLo := (597416105421561292927/100000000000000000000)
  directionHi := (4667313323605947601/781250000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree144.table
  base := (11065066789330333264809399288610345514803/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-681106695969444174495689418097416685000000000000)
      constant := (26152970508335617093071774176428521470288212507736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree144.table
  base := (11065066789319015045570360285058274291863/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-681859984583311458668010144392414185000000000000)
      constant := (26209405455542230608068979359473542198071557134456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597416105421561292927/100000000000000000000)
  centralHi := (4667313323605947601/781250000000000000)
  directionLo := (149875333442500336067/25000000000000000000)
  directionHi := (599501333770001344269/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree145.table
  base := (4525205374074650009227204541721788857079/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-685835046749321680174003710344099603750000000000)
      constant := (26522885580624644756071096907697969425354246660620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree145.table
  base := (9050410748141605138573178614239077151113/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-686593566534118598264187775016145697500000000000)
      constant := (26580106938315837743385561674314488184792576150570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149875333442500336067/25000000000000000000)
  centralHi := (599501333770001344269/100000000000000000000)
  directionLo := (18799354194540621571/3125000000000000000)
  directionHi := (601579334225299890273/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree146.table
  base := (46254023792732796767483051961918182358909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-690563397529199185852318002590782522500000000000)
      constant := (26895408827862057305191131784215689025002142361802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree146.table
  base := (18501609517080040598344879158327574743383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-691327148484925737860365405639877210000000000000)
      constant := (26953422037432695721497459779047377627674027335435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18799354194540621571/3125000000000000000)
  centralHi := (601579334225299890273/100000000000000000000)
  directionLo := (603650181431182533251/100000000000000000000)
  directionHi := (150912545357795633313/25000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree147.table
  base := (4726617731331745870348044461153973050433/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-695291748309076691530632294837465441250000000000)
      constant := (27270540250048404493732974416509767366761395390740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree147.table
  base := (47266177313289675796992967058873004290553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-696060730435732877456543036263608722500000000000)
      constant := (27329350752893356548529062927667620958959238210434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603650181431182533251/100000000000000000000)
  centralHi := (150912545357795633313/25000000000000000000)
  directionLo := (302856974377693714111/50000000000000000000)
  directionHi := (605713948755387428223/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree148.table
  base := (3018032143908598120466338763720486729519/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-700020099088954197208946587084148360000000000000)
      constant := (27648279847184233836875121060025510103765101926112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree148.table
  base := (3863081144201116992851077970461584129989/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-700794312386540017052720666887340235000000000000)
      constant := (27707893084698369655859940446239568633214159175525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302856974377693714111/50000000000000000000)
  centralHi := (605713948755387428223/100000000000000000000)
  directionLo := (75971338539999394089/12500000000000000000)
  directionHi := (607770708319995152713/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree149.table
  base := (19728413904171981230754086001813336535687/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-704748449868831702887260879330831278750000000000)
      constant := (28028627619270088990591449346039127334990403050715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree149.table
  base := (98642069520819788723348387666159973635613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-705527894337347156648898297511071747500000000000)
      constant := (28089049032848280329243432249240723284084498735557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75971338539999394089/12500000000000000000)
  centralHi := (607770708319995152713/100000000000000000000)
  directionLo := (304910265515418955237/50000000000000000000)
  directionHi := (24392821241233516419/4000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree150.table
  base := (100727477374062161460606233226586273951099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-709476800648709208565575171577514197500000000000)
      constant := (28411583566306508442523809467496241489704144465811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree150.table
  base := (5036373868701403811048057532972777223731/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-710261476288154296245075928134803260000000000000)
      constant := (28472818597343628442409425257993480161480103081180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304910265515418955237/50000000000000000000)
  centralHi := (24392821241233516419/4000000000000000000)
  directionLo := (611863486606021997733/100000000000000000000)
  directionHi := (305931743303010998867/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree151.table
  base := (51416626082377004426864367779905410408811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-714205151428586714243889463824197116250000000000)
      constant := (28797147688294024464013374812688285591149675872358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree151.table
  base := (1285415652059063125894115845253379343549/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-714995058238961435841253558758534772500000000000)
      constant := (28859201778184947445464535247221080624655973508880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611863486606021997733/100000000000000000000)
  centralHi := (305931743303010998867/50000000000000000000)
  directionLo := (613899643603595992799/100000000000000000000)
  directionHi := (767374554504494991/125000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree152.table
  base := (104959393893006596953436836637565334417257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-1991505546283834404216630903243435000000000000)
      constant := (80845761731947817951544097133732168523498488393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree152.table
  base := (52479696946490997341409498156070495657093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3639922)
      previous := (1819961)
      next := (1819961)
      square := (12598862196844635864545480723350000000000000)
      linear := (-1993708144569996053843299693579685000000000000)
      constant := (81019940652002115141970097016429066131383789514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613899643603595992799/100000000000000000000)
  centralHi := (767374554504494991/125000000000000000)
  directionLo := (615929069448395734747/100000000000000000000)
  directionHi := (153982267362098933687/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree153.table
  base := (107105902558890032244608114678727712464823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-723661852988341725600518048317562953750000000000)
      constant := (29576100457124439424316785661779541348267670255247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree153.table
  base := (107105902558869132003714367069531833563617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-724462222140575715033608820005997797500000000000)
      constant := (29639808988907595189445849947730632562918557855913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615929069448395734747/100000000000000000000)
  centralHi := (153982267362098933687/25000000000000000000)
  directionLo := (617951830458095830561/100000000000000000000)
  directionHi := (308975915229047915281/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree154.table
  base := (54636389081236655996616649682730433079741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-6019753750150572159329192897225172500000000000)
      constant := (247681728131969960656196486296559003702273837338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree154.table
  base := (54636389081227778738550200023978823814129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-6026411604061015327518896286196110000000000000)
      constant := (248215148915619441188077203778306641249152392322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617951830458095830561/100000000000000000000)
  centralHi := (308975915229047915281/50000000000000000000)
  directionLo := (619967991868496168711/100000000000000000000)
  directionHi := (77495998983562021089/12500000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree155.table
  base := (11146002070382427430033531851362564692669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-733118554548096736957146632810928791250000000000)
      constant := (30365485925765440512655728849766867552943839555410) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree155.table
  base := (111460020703809192677389212419727963147669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-733929386042189994225964081253460822500000000000)
      constant := (30430870665020336552293010522908723241463562700541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (619967991868496168711/100000000000000000000)
  centralHi := (77495998983562021089/12500000000000000000)
  directionLo := (155494404464517679253/25000000000000000000)
  directionHi := (621977617858070717013/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree156.table
  base := (113667630183009562385882624346823453910067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-4365958019692155281866632692648590000000000000)
      constant := (182036040961634066332933144242225438415245636627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree156.table
  base := (22733526036599350358532078217520985332383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-4370786792857971206048175809924215000000000000)
      constant := (182427940399995504054004868606691810801519109115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155494404464517679253/25000000000000000000)
  centralHi := (621977617858070717013/100000000000000000000)
  directionLo := (623980771571804740531/100000000000000000000)
  directionHi := (155995192892951185133/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree157.table
  base := (57947803300047300329183290930980086077881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-742575256107851748313775217304294628750000000000)
      constant := (31165304094220998301035948035529978033707594446818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree157.table
  base := (115895606600083719564448343823487250100543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-743396549943804273418319342500923847500000000000)
      constant := (31232386806527146696448927466776129933576217374327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623980771571804740531/100000000000000000000)
  centralHi := (155995192892951185133/25000000000000000000)
  directionLo := (39123594696521593/6250000000000000)
  directionHi := (625977515144345488001/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree158.table
  base := (59071974977571790258053501008591603569187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-747303606887729253992089509550977547500000000000)
      constant := (31569125440880437651581900120504723799869662183286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree158.table
  base := (11814394995513433868008516760414037522817/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-748130131894611413014496973124655360000000000000)
      constant := (31637065301804530331494809252083478389052746247130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39123594696521593/6250000000000000)
  centralHi := (625977515144345488001/100000000000000000000)
  directionLo := (627967909722490359771/100000000000000000000)
  directionHi := (156991977430622589943/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree159.table
  base := (30103165062054863538858524923734713722053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-752031957667606759670403801797660466250000000000)
      constant := (31975554962494939980619612751511679485678803534868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree159.table
  base := (24082532049642320986867010353883024505627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-752863713845418552610674603748386872500000000000)
      constant := (32044357413431856130828043130172591395417347574015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627967909722490359771/100000000000000000000)
  centralHi := (156991977430622589943/25000000000000000000)
  directionLo := (629952015487035583987/100000000000000000000)
  directionHi := (157488003871758895997/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree160.table
  base := (61350868739691967469126361291041796040263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-756760308447484265348718094044343385000000000000)
      constant := (32384592659064960861679156723706663732178138098814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree160.table
  base := (61350868739688634374116239440470539700639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-757597295796225692206852234372118385000000000000)
      constant := (32454263141409579941552493123382366551896300909742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629952015487035583987/100000000000000000000)
  centralHi := (157488003871758895997/25000000000000000000)
  directionLo := (631929891674007487753/100000000000000000000)
  directionHi := (315964945837003743877/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree161.table
  base := (2500223632973950062104266046776647554899/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-761488659227361771027032386291026303750000000000)
      constant := (32796238530590946765279754941493801126055777700550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree161.table
  base := (125011181648691841861490246509979702207927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-762330877747032831803029864995849897500000000000)
      constant := (32866782485738148466716263937822839771611163619503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631929891674007487753/100000000000000000000)
  centralHi := (315964945837003743877/50000000000000000000)
  directionLo := (633901596595297554177/100000000000000000000)
  directionHi := (316950798297648777089/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree162.table
  base := (127340992756219415817618866157625159750521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-766217010007239276705346678537709222500000000000)
      constant := (33210492577073335133060033707577103489636313818369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree162.table
  base := (5093639710248584328290573673003144915031/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-767064459697839971399207495619581410000000000000)
      constant := (33281915446417999345590183121655087674191406993975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633901596595297554177/100000000000000000000)
  centralHi := (316950798297648777089/50000000000000000000)
  directionLo := (635867187658721601901/100000000000000000000)
  directionHi := (317933593829360800951/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree163.table
  base := (12969117080200772067704835028831644911219/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-770945360787116782383660970784392141250000000000)
      constant := (33627354798512554477581085269878323060283595064910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree163.table
  base := (32422792700500909535023789720462631100979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-771798041648647110995385126243312922500000000000)
      constant := (33699662023449561258699729417892714035065129860524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (635867187658721601901/100000000000000000000)
  centralHi := (317933593829360800951/50000000000000000000)
  directionLo := (25513068855500904361/4000000000000000000)
  directionHi := (318913360693761304513/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree164.table
  base := (26412343157223854402266770539030060754567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-775673711566994288061975263031075060000000000000)
      constant := (34046825194909024502551001352626228291453103752315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree164.table
  base := (6603085789305790266212521892846411410729/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-776531623599454250591562756867044435000000000000)
      constant := (34120022216833254052496283404348498062292340657620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25513068855500904361/4000000000000000000)
  centralHi := (318913360693761304513/50000000000000000000)
  directionLo := (639780253439335925979/100000000000000000000)
  directionHi := (31989012671966796299/5000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree165.table
  base := (26890525541721949866618973410853943867861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-6449603821048527220994128556014528750000000000)
      constant := (284866973274902117678408394060107801268109158745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree165.table
  base := (26890525541721361140898437140214677677321/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (10859602)
      previous := (5429801)
      next := (5429801)
      square := (37588340934387715265296847447350000000000000)
      linear := (-6456737235952573472625953615626247500000000000)
      constant := (285479306004706519664471217356624635570828384445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639780253439335925979/100000000000000000000)
  centralHi := (31989012671966796299/5000000000000000000)
  directionLo := (320863919312317440049/50000000000000000000)
  directionHi := (641727838624634880099/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree166.table
  base := (136863906569533677475966895116058376047123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-785130413126749299418603847524440897500000000000)
      constant := (34893590512575352194364935723299758157894080179947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree166.table
  base := (43796450102249976984917468452841042037/3200000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-785998787501068529783918018114507460000000000000)
      constant := (34968583452658668349667682682206278635530860290625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320863919312317440049/50000000000000000000)
  centralHi := (641727838624634880099/100000000000000000000)
  directionLo := (643669530924674066491/100000000000000000000)
  directionHi := (160917382731168516623/25000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree167.table
  base := (27859110473788889599377103800824336692373/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-789858763906626805096918139771123816250000000000)
      constant := (35320885433846006509608708513209635039106253035985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree167.table
  base := (69647776184471162933168471931648114976503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-790732369451875669380095648738238972500000000000)
      constant := (35396784495101186692110106085873017153346306109534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643669530924674066491/100000000000000000000)
  centralHi := (160917382731168516623/25000000000000000000)
  directionLo := (322802691754473471799/50000000000000000000)
  directionHi := (645605383508946943599/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree168.table
  base := (141747565106894341502764128920067851002451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-794587114686504310775232432017806735000000000000)
      constant := (35750788530075505124911942712762674342138832500139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree168.table
  base := (35436891276723134939583633986038319171159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1314011842)
      previous := (657005921)
      next := (657005921)
      square := (4548189253060913547100918541129350000000000000)
      linear := (-795465951402682808976273279361970485000000000000)
      constant := (35827599153897429921244169603481984723127607884604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell108.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322802691754473471799/50000000000000000000)
  centralHi := (645605383508946943599/100000000000000000000)
  directionLo := (647535448752173705961/100000000000000000000)
  directionHi := (323767724376086852981/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree169.table
  base := (144219944783434550618713124730184637518799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-4729677310451963410967732096239583750000000000)
      constant := (214102365687953999696978384192884026049896159119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree169.table
  base := (72109972391716510472342995412779459162813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (7775218)
      previous := (3887609)
      next := (3887609)
      square := (26912362444147417438466973616150000000000000)
      linear := (-4734908481381597328831070473288177500000000000)
      constant := (214562292479572639105428743658216004580131669306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell108.Kernel169
