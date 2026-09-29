import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell056.Parameters
import ForestUnimodality.BinomialMassData.Q24_49.Batch000_049
import ForestUnimodality.BinomialMassData.Q24_49.Batch050_099
import ForestUnimodality.BinomialMassData.Q24_49.Batch100_149
import ForestUnimodality.BinomialMassData.Q24_49.Batch150_199
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch000_049
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch050_099
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch100_149
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree000.table
  base := (859370912785660747046279081/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (86)
      previous := (43)
      next := (43)
      square := (321892818004492209382760850000000000000)
      linear := (7299210796991100706071487000000000000)
      constant := (429685456392830373523139540500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree000.table
  base := (859370912785660747046279081/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (86)
      previous := (43)
      next := (43)
      square := (321892818004492209382760850000000000000)
      linear := (7299210796991100706071487000000000000)
      constant := (429685456392830373523139540500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree001.table
  base := (122549070846691375000506368242443096317653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-739566502822990043672975878913000000000000)
      constant := (588657464597085308730605710481099748517369706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree001.table
  base := (12230691983599917082153154617043474752359/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-2422670023306624271461761250089396000000000000)
      constant := (1919348156497264833522825553118742994031248081060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24994793293705898961/50000000000000000000)
  directionHi := (49989586587411797923/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree002.table
  base := (73397449775935807856233040796968965593219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-1496658410769555720141229398113000000000000)
      constant := (353179027132931576307188262768020972778637638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree002.table
  base := (36570194745310212406508641660294472833307/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-4902595545151970135265694550996421000000000000)
      constant := (1149815701626727179795125234807362880536559758276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24994793293705898961/50000000000000000000)
  centralHi := (49989586587411797923/100000000000000000000)
  directionLo := (17673987832335482587/25000000000000000000)
  directionHi := (70695951329341930349/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree003.table
  base := (46609721704899826116406737851451190130503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-2253750318716121396609482917313000000000000)
      constant := (225462824379772468021134367202932615006675406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree003.table
  base := (185602369601526914077202609262710671798147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (149908836)
      previous := (74954418)
      next := (74954418)
      square := (561099740276898486972534389417100000000000000)
      linear := (-1640560237110514666459917300422988000000000000)
      constant := (162963265725569198084426656528984371494408393761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17673987832335482587/25000000000000000000)
  centralHi := (70695951329341930349/100000000000000000000)
  directionLo := (17316900763752184271/20000000000000000000)
  directionHi := (21646125954690230339/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree004.table
  base := (126066386627946542736104983768500175594769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-6021684453325374146155472873026000000000000)
      constant := (308549851739980357237288393465672921603040369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree004.table
  base := (15680311416002733178751770895008515960793/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-9862446588842661862873561152810471000000000000)
      constant := (501620004363239975812529795066171618068118660524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17316900763752184271/20000000000000000000)
  centralHi := (21646125954690230339/25000000000000000000)
  directionLo := (24994793293705898961/25000000000000000000)
  directionHi := (19995834634964719169/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree005.table
  base := (4524980177822578519279080501757145000103/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-3767934134609252749545989955713000000000000)
      constant := (113237111289298490390850778743629051452473030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree005.table
  base := (22511214857762974641128255372243422125429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-12342372110688007726677494453717496000000000000)
      constant := (368241525305421341538244905499322557547294959486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24994793293705898961/25000000000000000000)
  centralHi := (19995834634964719169/20000000000000000000)
  directionLo := (2235602275531290259/2000000000000000000)
  directionHi := (111780113776564512951/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree006.table
  base := (68342346825552870492992213280046666338993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-9050052085111636852028486949826000000000000)
      constant := (177336507213667604548032081232048045879922193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree006.table
  base := (4250457544136989308592623910052577313251/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-548973986390124207054867694615723000000000000)
      constant := (10684430805619169130921676664644191508983950168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2235602275531290259/2000000000000000000)
  centralHi := (111780113776564512951/100000000000000000000)
  directionLo := (122448979591836734693/100000000000000000000)
  directionHi := (61224489795918367347/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree007.table
  base := (26826503361031901167944964263704444459689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (4214)
      previous := (2107)
      next := (2107)
      square := (15772748082220118259755281650000000000000)
      linear := (-107798325520456818418010142737000000000000)
      constant := (1498682660447256164915153488705517778524761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree007.table
  base := (26699372815512384232423389587880567736039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (13767138)
      previous := (6883569)
      next := (6883569)
      square := (51529567984613126354620505150550000000000000)
      linear := (-353106594987320397026231858276154000000000000)
      constant := (4879025204538175811652260821841891049888331237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122448979591836734693/100000000000000000000)
  centralHi := (61224489795918367347/50000000000000000000)
  directionLo := (66130007126610818683/50000000000000000000)
  directionHi := (132260014253221637367/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree008.table
  base := (43291910536171964608495346229392765387613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-12078419716897899557901501026626000000000000)
      constant := (127539048932827904087484077146180029695658813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree008.table
  base := (8618314885847472564665712265624760646509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-39564297352448090636178588712877142000000000000)
      constant := (415505881802854008186403913820850132850899560515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66130007126610818683/50000000000000000000)
  centralHi := (132260014253221637367/100000000000000000000)
  directionLo := (17673987832335482587/12500000000000000000)
  directionHi := (141391902658683860697/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree009.table
  base := (17784294530544376234674298007030138946899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-6796301766395515455419004032513000000000000)
      constant := (57641067637579282050542019114071363611504499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree009.table
  base := (35404879255096939084568993350083510779873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (187033246758966162324178129805700000000000000)
      linear := (-1649042533190325272732831678321896000000000000)
      constant := (13920673634580767350521800546101819385279483833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17673987832335482587/12500000000000000000)
  centralHi := (141391902658683860697/100000000000000000000)
  directionLo := (149968759762235393767/100000000000000000000)
  directionHi := (18746094970279424221/12500000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree010.table
  base := (3693506680325504106798331589399503603331/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-7553393674342081131887257551713000000000000)
      constant := (53927625755932277357834800857472832606390924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree010.table
  base := (7352548646810595509131572816297435500621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-24741999719914737045697160958252621000000000000)
      constant := (175959221640237420728500351500699011990099331214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149968759762235393767/100000000000000000000)
  centralHi := (18746094970279424221/12500000000000000000)
  directionLo := (79040476453212589493/50000000000000000000)
  directionHi := (158080952906425178987/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree011.table
  base := (987748470913920633976658789617870922039/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-16620971164577293616711022141826000000000000)
      constant := (103970040472150510347263262738348702095390975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree011.table
  base := (6143766050271661029598825798672551889799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 324135000000000000000000000000000000000000000
      center := (5575122)
      previous := (2787561)
      next := (2787561)
      square := (20867345712777216457656237622950000000000000)
      linear := (-224974588774876718260339621976526000000000000)
      constant := (1402933987367803837876024765738380167719999546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79040476453212589493/50000000000000000000)
  centralHi := (158080952906425178987/100000000000000000000)
  directionLo := (82898351067713881229/50000000000000000000)
  directionHi := (165796702135427762459/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree012.table
  base := (20682752817211572731716053656065974843287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-18135154980470424969647529180226000000000000)
      constant := (102851432381719912932609515063926405598732087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree012.table
  base := (20579178060338511926709705511171268442299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (149908836)
      previous := (74954418)
      next := (74954418)
      square := (561099740276898486972534389417100000000000000)
      linear := (-6600411280801206394067783902237038000000000000)
      constant := (37346711081760118993665845654389270237375443337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82898351067713881229/50000000000000000000)
  centralHi := (165796702135427762459/100000000000000000000)
  directionLo := (17316900763752184271/10000000000000000000)
  directionHi := (173169007637521842711/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree013.table
  base := (692400978642339111392279887782212374439/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-19649338796363556322584036218626000000000000)
      constant := (104006857025336184526443702842415297775700975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree013.table
  base := (8609425261821879915918341719483260892567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-32181776285450774637108960860973696000000000000)
      constant := (170075921920625975708013785622463542444775349989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17316900763752184271/10000000000000000000)
  centralHi := (173169007637521842711/100000000000000000000)
  directionLo := (180240017680160139893/100000000000000000000)
  directionHi := (90120008840080069947/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree014.table
  base := (14437440552665663523230776142263493387397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (8428)
      previous := (4214)
      next := (4214)
      square := (31545496164440236519510563300000000000000)
      linear := (-431908624739932401541235576674000000000000)
      constant := (2185811622789739593799589988506911175982453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree014.table
  base := (112162809489289689935300773285376198749/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (13767138)
      previous := (6883569)
      next := (6883569)
      square := (51529567984613126354620505150550000000000000)
      linear := (-707381669536655520426793758405729000000000000)
      constant := (3576814510217923765004877547487225193557514688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180240017680160139893/100000000000000000000)
  centralHi := (90120008840080069947/50000000000000000000)
  directionLo := (46760976479141224557/25000000000000000000)
  directionHi := (187043905916564898229/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree015.table
  base := (5983455329801132153629527661091215357397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-11338853214074909514228525147713000000000000)
      constant := (55954827381775785620415201043600008073110197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree015.table
  base := (5947769495207000950322083416213416673487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-1375615827005239494989512128251398000000000000)
      constant := (6786716731906952082179976384441692400398116727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46760976479141224557/25000000000000000000)
  centralHi := (187043905916564898229/100000000000000000000)
  directionLo := (96804418168419775469/50000000000000000000)
  directionHi := (193608836336839550939/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree016.table
  base := (9825504747956894718538824471407295991069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-24191890244042950381393557333826000000000000)
      constant := (118246407742472941570929603152264917674556669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree016.table
  base := (9762300811970728602457220141950745111457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-79243105701973624457041521527389542000000000000)
      constant := (387446633889369355161566678087286427354191175619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96804418168419775469/50000000000000000000)
  centralHi := (193608836336839550939/100000000000000000000)
  directionLo := (199958346349647191689/100000000000000000000)
  directionHi := (19995834634964719169/10000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree017.table
  base := (7957047197662469615459855100490768433597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-25706074059936081734330064372226000000000000)
      constant := (125980150789680279661471354028870335009066397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree017.table
  base := (7901121618203549223579096762353341867087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-84202956745664316184649388129203592000000000000)
      constant := (412980318199471705126941648393309436529335522829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199958346349647191689/100000000000000000000)
  centralHi := (19995834634964719169/10000000000000000000)
  directionLo := (103056172840429366871/50000000000000000000)
  directionHi := (206112345680858733743/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree018.table
  base := (6317142442439154550386979814346394779793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-27220257875829213087266571410626000000000000)
      constant := (135004290150535703003683617801413693866282993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree018.table
  base := (313385973493275749135601184283760208833/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-1651163107210277924301060272796623000000000000)
      constant := (8198822332498879010143991800975836996303719930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103056172840429366871/50000000000000000000)
  centralHi := (206112345680858733743/100000000000000000000)
  directionLo := (53021963497006447761/25000000000000000000)
  directionHi := (42417570797605158209/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree019.table
  base := (4870074325624604572812594365346750425003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-28734441691722344440203078449026000000000000)
      constant := (145233071332892921371397636671341547770432203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree019.table
  base := (1206615310826851767572026731310242848963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-47061329416522849819932560666415846000000000000)
      constant := (238217694273224441292078801592532537512073305042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53021963497006447761/25000000000000000000)
  centralHi := (42417570797605158209/20000000000000000000)
  directionLo := (27237444520488038803/12500000000000000000)
  directionHi := (8715982246556172417/4000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree020.table
  base := (3586761636894234326524592050244321392967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-30248625507615475793139585487426000000000000)
      constant := (156596670350762605324348142444156615664513767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree020.table
  base := (3548332767053751625724164008519201899623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-99082509876736391367472987934645742000000000000)
      constant := (513849676868996847416924643802656780487170086741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27237444520488038803/12500000000000000000)
  centralHi := (8715982246556172417/4000000000000000000)
  directionLo := (2235602275531290259/1000000000000000000)
  directionHi := (223560227553129025901/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree021.table
  base := (2443334407695666124927342558182862560431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (8428)
      previous := (4214)
      next := (4214)
      square := (31545496164440236519510563300000000000000)
      linear := (-648220598438951166246450867874000000000000)
      constant := (3449750518564295837490184219254960265461119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree021.table
  base := (2409522404057266150326054871717182963/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88935000000000000000000000000000000000000000
      center := (1529682)
      previous := (764841)
      next := (764841)
      square := (5725507553845902928291167238950000000000000)
      linear := (-117961860453998960425261739837256000000000000)
      constant := (629016429530844438728336090632308391681440500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2235602275531290259/1000000000000000000)
  centralHi := (223560227553129025901/100000000000000000000)
  directionLo := (229081064496363758301/100000000000000000000)
  directionHi := (114540532248181879151/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree022.table
  base := (710046985200278506151266842209945116463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-16638496569700869249506299782113000000000000)
      constant := (91254545004290471036365310982882078224627663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree022.table
  base := (1390384526572745257309369448853058052821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (11150244)
      previous := (5575122)
      next := (5575122)
      square := (41734691425554432915312475245900000000000000)
      linear := (-900844726976179957212303480481602000000000000)
      constant := (4951320073204812191949282152703691194390226967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229081064496363758301/100000000000000000000)
  centralHi := (114540532248181879151/50000000000000000000)
  directionLo := (117235972378327115507/50000000000000000000)
  directionHi := (46894388951330846203/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree023.table
  base := (50072379395098709492792652900418928901/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-17395588477647434925974553301313000000000000)
      constant := (98485719078241938883327916256093529241456505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree023.table
  base := (94930361631122969821390146314365086723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-113962063007808466550296587740087892000000000000)
      constant := (646673788905187177211555452847952486263580112205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117235972378327115507/50000000000000000000)
  centralHi := (46894388951330846203/20000000000000000000)
  directionLo := (11987081759664010803/5000000000000000000)
  directionHi := (239741635193280216061/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree024.table
  base := (-2052041236754322649512941172817080151/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-18152680385594000602442806820513000000000000)
      constant := (106196142579968360139328256380037295244595920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree024.table
  base := (-351180330567848307577147683221045205981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (187033246758966162324178129805700000000000000)
      linear := (-4404515335240709565848313123774146000000000000)
      constant := (25828842228259451771631086467993742725713193899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11987081759664010803/5000000000000000000)
  centralHi := (239741635193280216061/100000000000000000000)
  directionLo := (244897959183673469387/100000000000000000000)
  directionHi := (61224489795918367347/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree025.table
  base := (-269583076634311741003801737545515939413/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-18909772293540566278911060339713000000000000)
      constant := (114372279750187692036735148338506432458938774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree025.table
  base := (-1098344267601741301004812359789157075143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-123881765095189850005512320943715992000000000000)
      constant := (751136475105602873258483634084298827279054273419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244897959183673469387/100000000000000000000)
  centralHi := (61224489795918367347/25000000000000000000)
  directionLo := (249947932937058989611/100000000000000000000)
  directionHi := (62486983234264747403/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree026.table
  base := (-219836155316089949425020581438068562089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-19666864201487131955379313858913000000000000)
      constant := (123002850798332630751155149278956789529697244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree026.table
  base := (-444049089388405612801586749799386909897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-64420808069440270866560093772765021000000000000)
      constant := (403936800930281378658081603465926841039689937802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249947932937058989611/100000000000000000000)
  centralHi := (62486983234264747403/25000000000000000000)
  directionLo := (254897877485648906361/100000000000000000000)
  directionHi := (127448938742824453181/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree027.table
  base := (-2377236969520286287838535578059769973051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-40847912218867395263695134756226000000000000)
      constant := (264156888656446263140978936283430492294704549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree027.table
  base := (-2392539777791346233981309553317198324229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (187033246758966162324178129805700000000000000)
      linear := (-4955609895650786424471409412864596000000000000)
      constant := (32130700436362907994542831186430994975646666691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254897877485648906361/100000000000000000000)
  centralHi := (127448938742824453181/50000000000000000000)
  directionLo := (51950702291256552813/20000000000000000000)
  directionHi := (129876755728141382033/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree028.table
  base := (-735130855207742638344005197350973703471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (4214)
      previous := (2107)
      next := (2107)
      square := (15772748082220118259755281650000000000000)
      linear := (-432266286068984965475833079537000000000000)
      constant := (2889616317263463403439331444995604577059842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree028.table
  base := (-1476944604181108774313904336216447592951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (13767138)
      previous := (6883569)
      next := (6883569)
      square := (51529567984613126354620505150550000000000000)
      linear := (-1415931818635325767227917558664879000000000000)
      constant := (9490319421250362510902456348607499419977625067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51950702291256552813/20000000000000000000)
  centralHi := (129876755728141382033/50000000000000000000)
  directionLo := (264520028506443274733/100000000000000000000)
  directionHi := (132260014253221637367/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree029.table
  base := (-138160915027034600099273188366959489639/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-43876279850653657969568148833026000000000000)
      constant := (303069089158389275332800362710177256634419025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree029.table
  base := (-866422180570597168074320010833709945213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-71860584634976308457971893675486096000000000000)
      constant := (497699036344641098709668808324087281287365797458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264520028506443274733/100000000000000000000)
  centralHi := (132260014253221637367/50000000000000000000)
  directionLo := (16825135150858315269/6250000000000000000)
  directionHi := (53840432482746608861/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree030.table
  base := (-1961157991838216057272059875567379489421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-22695231833273394661252327935713000000000000)
      constant := (161902980358207358557602806817402721845900179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree030.table
  base := (-3932491679828215420072026286286202332333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (149908836)
      previous := (74954418)
      next := (74954418)
      square := (561099740276898486972534389417100000000000000)
      linear := (-16520113368182589849283517105865138000000000000)
      constant := (118170389237661739597333548135548428636624853521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16825135150858315269/6250000000000000000)
  centralHi := (53840432482746608861/20000000000000000000)
  directionLo := (273804242142831391397/100000000000000000000)
  directionHi := (136902121071415695699/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree031.table
  base := (-4349238770613776987775003096579888474499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-46904647482439920675441162909826000000000000)
      constant := (345383803467995305543462953036167687772727901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree031.table
  base := (-2179054785289367841299774480159014752619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-76820435678667000185579760277300146000000000000)
      constant := (567213848525964063964327998133587421751468138527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273804242142831391397/100000000000000000000)
  centralHi := (136902121071415695699/50000000000000000000)
  directionLo := (55666047742799411807/20000000000000000000)
  directionHi := (69582559678499264759/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree032.table
  base := (-118450154449596514503210509545228268339/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-24209415649166526014188834974113000000000000)
      constant := (183897449169299619178762484723254138554361220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree032.table
  base := (-593216920918077754940422917515627813861/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-79300361200512346049383693578207171000000000000)
      constant := (604027804267771759023756539489161439524043149252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55666047742799411807/20000000000000000000)
  centralHi := (69582559678499264759/25000000000000000000)
  directionLo := (17673987832335482587/6250000000000000000)
  directionHi := (282783805317367721393/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree033.table
  base := (-318207164321978741630590974059995137307/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-24966507557113091690657088493313000000000000)
      constant := (195516385607863602920826488117159613402607144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree033.table
  base := (-1274511473765660446196059818134372399157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-25032227340789008850072735500188000000000000)
      constant := (196571202999028245074302656762669618739248086) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17673987832335482587/6250000000000000000)
  centralHi := (282783805317367721393/100000000000000000000)
  directionLo := (143584155912962129221/50000000000000000000)
  directionHi := (287168311825924258443/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree034.table
  base := (-1352856820654231099466896916743039480879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-25723599465059657367125342012513000000000000)
      constant := (207545994127910654660496007207191924412819042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree034.table
  base := (-169290215107871382170394507476781002857/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-84260212244203037776991560180021221000000000000)
      constant := (681715988488934402998788267391793875908200009296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143584155912962129221/50000000000000000000)
  centralHi := (287168311825924258443/100000000000000000000)
  directionLo := (145743437317201020367/50000000000000000000)
  directionHi := (58297374926880408147/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree035.table
  base := (-5700244968879851576983044997156666071241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (8428)
      previous := (4214)
      next := (4214)
      square := (31545496164440236519510563300000000000000)
      linear := (-1080844545836988695656881450274000000000000)
      constant := (8978938480915317853765143176979323362509191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree035.table
  base := (-2852671853080257893666049559006047801529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (13767138)
      previous := (6883569)
      next := (6883569)
      square := (51529567984613126354620505150550000000000000)
      linear := (-1770206893184660890628479458794454000000000000)
      constant := (14746408462091653309354460705140352974787833093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145743437317201020367/50000000000000000000)
  centralHi := (58297374926880408147/20000000000000000000)
  directionLo := (295742382575294664769/100000000000000000000)
  directionHi := (29574238257529466477/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree036.table
  base := (-5959365271909459064491634905069350307887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-54475566561905577440123698101826000000000000)
      constant := (465656927343705390977957986608864489910763313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree036.table
  base := (-1490950067959316050173873525425325342597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-3304446788440508500170349140067973000000000000)
      constant := (28324666167248661266626455369167871112286753926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295742382575294664769/100000000000000000000)
  centralHi := (29574238257529466477/10000000000000000000)
  directionLo := (149968759762235393767/50000000000000000000)
  directionHi := (59987503904894157507/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree037.table
  base := (-6190131781256410880712605800882308658147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-55989750377798708793060205140226000000000000)
      constant := (492155587633874613438603411792193576911789053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree037.table
  base := (-3096994048057432110624140237345360990007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-91699988809739075368403360082742296000000000000)
      constant := (808286681859685569727622388128187628880198761531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149968759762235393767/50000000000000000000)
  centralHi := (59987503904894157507/20000000000000000000)
  directionLo := (304074784199006933047/100000000000000000000)
  directionHi := (38009348024875866631/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree038.table
  base := (-6393675185803138964561696747237962273617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-57503934193691840145996712178626000000000000)
      constant := (519461251651351523131091601732569652581045583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree038.table
  base := (-6397027227280614873767608210451339450253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-188359828663168842464414586767298642000000000000)
      constant := (1706263415615003508689599083606730639112472301049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304074784199006933047/100000000000000000000)
  centralHi := (38009348024875866631/12500000000000000000)
  directionLo := (308156507562071416213/100000000000000000000)
  directionHi := (154078253781035708107/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree039.table
  base := (-6570947589332710736578990601936022654837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-59018118009584971498933219217026000000000000)
      constant := (547571633394952975178705817488415609605736363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree039.table
  base := (-6573860406719940622286690986951299456911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (149908836)
      previous := (74954418)
      next := (74954418)
      square := (561099740276898486972534389417100000000000000)
      linear := (-21479964411873281576891383707679188000000000000)
      constant := (199843859310192652642397321518981402841436278107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308156507562071416213/100000000000000000000)
  centralHi := (154078253781035708107/50000000000000000000)
  directionLo := (156092434089575045817/50000000000000000000)
  directionHi := (62436973635830018327/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree040.table
  base := (-210085974666047569729435690787552962989/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-30266150912739051425934863127713000000000000)
      constant := (288242403394278675351212795114225365373814576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree040.table
  base := (-336264080289653605223676119087030737327/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-99139765375275112959815159985463371000000000000)
      constant := (946780545142508252236927370535404610653476110910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156092434089575045817/50000000000000000000)
  centralHi := (62436973635830018327/20000000000000000000)
  directionLo := (316161905812850357973/100000000000000000000)
  directionHi := (158080952906425178987/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree041.table
  base := (-3424881131932802409210564980817340245739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-31023242820685617102403116646913000000000000)
      constant := (303099574044199227191955980241465566069980661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree041.table
  base := (-6851959883920566681315811894187387328911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-203239381794240917647238186572740792000000000000)
      constant := (1991157236947929567649504846317080576487071078963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316161905812850357973/100000000000000000000)
  centralHi := (158080952906425178987/50000000000000000000)
  directionLo := (320089533497104529269/100000000000000000000)
  directionHi := (32008953349710452927/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree042.table
  base := (-6952551250043009271085984973158849882867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (8428)
      previous := (4214)
      next := (4214)
      square := (31545496164440236519510563300000000000000)
      linear := (-1297156519536007460362096741474000000000000)
      constant := (12994148728063459394215204589723216355739517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree042.table
  base := (-695445935051474664358330112030595988549/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (509894)
      previous := (254947)
      next := (254947)
      square := (1908502517948634309430389079650000000000000)
      linear := (-78684517323481333852927457737927000000000000)
      constant := (790392573268498668418040391064936981919464895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320089533497104529269/100000000000000000000)
  centralHi := (32008953349710452927/10000000000000000000)
  directionLo := (80992387073405834403/25000000000000000000)
  directionHi := (323969548293623337613/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree043.table
  base := (-7031599563073190529294602246365696362907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-65074853273157496910679247370626000000000000)
      constant := (668026069670729399189485397118043963032660293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree043.table
  base := (-7033255879703650292015139779801794961853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-213159083881622301102453919776368892000000000000)
      constant := (2194221893258026332418180786468636385848962623849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80992387073405834403/25000000000000000000)
  centralHi := (323969548293623337613/100000000000000000000)
  directionLo := (81950910225556176227/25000000000000000000)
  directionHi := (327803640902224704909/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree044.table
  base := (-55369638249639728167354784678368207913/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-33294518544525314131807877204513000000000000)
      constant := (350068259042785277698211034569455227699256768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree044.table
  base := (-7088751116438631591712909312122716097347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (11150244)
      previous := (5575122)
      next := (5575122)
      square := (41734691425554432915312475245900000000000000)
      linear := (-1802635825829032998595551953538702000000000000)
      constant := (19005648922204607460815455494483758683557286031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81950910225556176227/25000000000000000000)
  centralHi := (327803640902224704909/100000000000000000000)
  directionLo := (82898351067713881229/25000000000000000000)
  directionHi := (331593404270855524917/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree045.table
  base := (-7120037047677053875200847278258124159083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-68103220904943759616552261447426000000000000)
      constant := (733043808418653281595016670380822243894041717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree045.table
  base := (-1780321055347593885085339542486281341059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-4131088629055623788104993573703648000000000000)
      constant := (44588166063992895733296772767566267992028396522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82898351067713881229/25000000000000000000)
  centralHi := (331593404270855524917/100000000000000000000)
  directionLo := (335340341329693538851/100000000000000000000)
  directionHi := (83835085332423384713/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree046.table
  base := (-3565029926471310367521680170994193037967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-34808702360418445484744384242913000000000000)
      constant := (383373621908231529894843850902290942515841233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree046.table
  base := (-7131141726618171678001812893434456282921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-228038637012694376285277519581811042000000000000)
      constant := (2518451989287932217811293638146831546808196720293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335340341329693538851/100000000000000000000)
  centralHi := (83835085332423384713/25000000000000000000)
  directionLo := (339045871955839789901/100000000000000000000)
  directionHi := (169522935977919894951/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree047.table
  base := (-1779406880942669340829975978036682680801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-35565794268365011161212637762113000000000000)
      constant := (400623117522369825050383253490403849766793598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree047.table
  base := (-7118565811559420805872940297686756064453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-232998488056385068012885386183625092000000000000)
      constant := (2631754685411972053208174699459004020667774349649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339045871955839789901/100000000000000000000)
  centralHi := (169522935977919894951/50000000000000000000)
  directionLo := (342711339260136024529/100000000000000000000)
  directionHi := (34271133926013602453/10000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree048.table
  base := (-7082947661647516446288244260569874067479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-72645772352623153675361782562626000000000000)
      constant := (836540283652314463788548189090819732363982921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree048.table
  base := (-1770940314287180994866394811171935432421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (74954418)
      previous := (37477209)
      next := (37477209)
      square := (280549870138449243486267194708550000000000000)
      linear := (-13219907727781986652249625154746619000000000000)
      constant := (152648191639575807916165065229193120877425711954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342711339260136024529/100000000000000000000)
  centralHi := (34271133926013602453/10000000000000000000)
  directionLo := (17316900763752184271/5000000000000000000)
  directionHi := (346338015275043685421/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree049.table
  base := (-1405239191176665029857887745335720119843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (172)
      previous := (86)
      next := (86)
      square := (643785636008984418765521700000000000000)
      linear := (-30887112106837269899332898626000000000000)
      constant := (363443968267036127225759629097321399400785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree049.table
  base := (-1756725323241564868373822588348870262243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (280962)
      previous := (140481)
      next := (140481)
      square := (1051623836420676048053479696950000000000000)
      linear := (-50586878413945533416930678756196000000000000)
      constant := (596873994744830567555366472034273106706504238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17316900763752184271/5000000000000000000)
  centralHi := (346338015275043685421/100000000000000000000)
  directionLo := (21870444131992661591/6250000000000000000)
  directionHi := (349927106111882585457/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree050.table
  base := (-694752114818501504589797306307583870341/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-37837069992204708190617398319713000000000000)
      constant := (454755965193209594227058103902177455636556295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree050.table
  base := (-1389626503339123013686938641951957036109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-247878041187457143195708985989067242000000000000)
      constant := (2987317955246855474587462053510611291138197923485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21870444131992661591/6250000000000000000)
  centralHi := (349927106111882585457/100000000000000000000)
  directionLo := (17673987832335482587/5000000000000000000)
  directionHi := (353479756646709651741/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree051.table
  base := (-6847049213795821559783118904302210640483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-77188323800302547734171303677826000000000000)
      constant := (947188868917551796491520282921346392252200317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree051.table
  base := (-6847579035577334391181950480844821019937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (187033246758966162324178129805700000000000000)
      linear := (-9364366378931401293456179725588196000000000000)
      constant := (115224206424199696323145768459045246502466882823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17673987832335482587/5000000000000000000)
  centralHi := (353479756646709651741/100000000000000000000)
  directionLo := (89249263696611741901/25000000000000000000)
  directionHi := (71399410957289393521/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree052.table
  base := (-1681221721221495115964769153618283817933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-39351253808097839543553905358113000000000000)
      constant := (492829763569305414745247049869701001106285734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree052.table
  base := (-840668244366937007341349947184974731703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-128898871637419263325462359596347671000000000000)
      constant := (1618697476465540617214162334264229854244858575596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89249263696611741901/25000000000000000000)
  centralHi := (71399410957289393521/20000000000000000000)
  directionLo := (180240017680160139893/50000000000000000000)
  directionHi := (360480035360320279787/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree053.table
  base := (-3290562310670279936588143744950675494637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-40108345716044405220022158877313000000000000)
      constant := (512461843927706119453400774353037428137376563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree053.table
  base := (-3290761159186712958324099317259388650767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-131378797159264609189266292897254696000000000000)
      constant := (1683170697607966683171084970658667577669344050611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180240017680160139893/50000000000000000000)
  centralHi := (360480035360320279787/100000000000000000000)
  directionLo := (90982420919015346343/25000000000000000000)
  directionHi := (363929683676061385373/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree054.table
  base := (-320791955848789782032449832154920808017/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-40865437623990970896490412396513000000000000)
      constant := (532490583463051621228797763653112351399511830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree054.table
  base := (-802022948396793820652124386820269026909/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-4957730469670739076039638007339323000000000000)
      constant := (64775783488603456685882790601302071488133481644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90982420919015346343/25000000000000000000)
  centralHi := (363929683676061385373/100000000000000000000)
  directionLo := (367346938775510204081/100000000000000000000)
  directionHi := (183673469387755102041/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree055.table
  base := (-389318463433844683822034744913406892171/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-41622529531937536572958665915713000000000000)
      constant := (552915904091040552548000157880543280415179432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree055.table
  base := (-3114696866110083155535273109696750395239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 324135000000000000000000000000000000000000000
      center := (5575122)
      previous := (2787561)
      next := (2787561)
      square := (20867345712777216457656237622950000000000000)
      linear := (-1126765687627729759643588095033626000000000000)
      constant := (15008459465475857333878274062772821887127841347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367346938775510204081/100000000000000000000)
  centralHi := (183673469387755102041/50000000000000000000)
  directionLo := (74146539284020204051/20000000000000000000)
  directionHi := (11585396763128156883/3125000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree056.table
  base := (-6020948694153083126436940630358980781377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (8428)
      previous := (4214)
      next := (4214)
      square := (31545496164440236519510563300000000000000)
      linear := (-1729780466934044989772527323874000000000000)
      constant := (23417866921199388461478861700856409941712527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree056.table
  base := (-1204241399974952780717677186471039748897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (27534276)
      previous := (13767138)
      next := (13767138)
      square := (103059135969226252709241010301100000000000000)
      linear := (-5666064233665332521660330318366358000000000000)
      constant := (76914400336439447800121868590938730719386607745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74146539284020204051/20000000000000000000)
  centralHi := (11585396763128156883/3125000000000000000)
  directionLo := (46760976479141224557/12500000000000000000)
  directionHi := (374087811833129796457/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree057.table
  base := (-289572288932183623356574545406650334381/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-43136713347830667925895172954113000000000000)
      constant := (594956033685833192192603102198602325471512190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree057.table
  base := (-1158333880673849890356217175933495163441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (149908836)
      previous := (74954418)
      next := (74954418)
      square := (561099740276898486972534389417100000000000000)
      linear := (-31399666499254665032107116911307288000000000000)
      constant := (434240802774982820050752242007109423024329358585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46760976479141224557/12500000000000000000)
  centralHi := (374087811833129796457/100000000000000000000)
  directionLo := (377413102222590394913/100000000000000000000)
  directionHi := (188706551111295197457/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree058.table
  base := (-2770313206703496418402913032264655238439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-43893805255777233602363426473313000000000000)
      constant := (616570738726520128503892801478636562772507961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree058.table
  base := (-554081998294539978780649057748847276051/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-143778424768491338508285959401789821000000000000)
      constant := (2025065854939411297940222143777328431969442302915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377413102222590394913/100000000000000000000)
  centralHi := (188706551111295197457/50000000000000000000)
  directionLo := (190354674552832960113/50000000000000000000)
  directionHi := (380709349105665920227/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree059.table
  base := (-5268524343338924808695462534285684163143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-89301794327447598557663359985026000000000000)
      constant := (1277163628361396643223863944062364072324293657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree059.table
  base := (-2634345935543939399604617806589078139919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-146258350290336684372089892702696846000000000000)
      constant := (2097349405652017504235306651195089021727239989427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190354674552832960113/50000000000000000000)
  centralHi := (380709349105665920227/100000000000000000000)
  directionLo := (191988650226803869481/50000000000000000000)
  directionHi := (383977300453607738963/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree060.table
  base := (-4975168226057361614901989766834501812111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-90815978143340729910599867023426000000000000)
      constant := (1321978451289794981383165311444390361149121489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree060.table
  base := (-621914149172363826469182685032368740541/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-5508825030080815934662734296429773000000000000)
      constant := (80404968678361689595847534784110099804517152556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191988650226803869481/50000000000000000000)
  centralHi := (383977300453607738963/100000000000000000000)
  directionLo := (387217672673679101877/100000000000000000000)
  directionHi := (193608836336839550939/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree061.table
  base := (-4660582404495103595371686368902923989293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-92330161959233861263536374061826000000000000)
      constant := (1367585887790853617869478690168600079501707507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree061.table
  base := (-4660707830653589563472656292078036494963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-302436402668054752199395518609021792000000000000)
      constant := (4491640014538440789057049686405160005755065065479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387217672673679101877/100000000000000000000)
  centralHi := (193608836336839550939/50000000000000000000)
  directionLo := (195215576221520316077/50000000000000000000)
  directionHi := (78086230488608126431/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree062.table
  base := (-2162393780532389722959222806702314720961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-46922172887563496308236440550113000000000000)
      constant := (706992944103049915592077461243363742354972639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree062.table
  base := (-540612008007997374072325778352046889861/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-153698126855872721963501692605417921000000000000)
      constant := (2322006884969024019550642407804248255435154781252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195215576221520316077/50000000000000000000)
  centralHi := (78086230488608126431/20000000000000000000)
  directionLo := (6150287475123058033/1562500000000000000)
  directionHi := (393618398407875714113/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree063.table
  base := (-3967801271757732215426801664580141930487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (8428)
      previous := (4214)
      next := (4214)
      square := (31545496164440236519510563300000000000000)
      linear := (-1946092440633063754477742615074000000000000)
      constant := (29819967557868947074833106976947573045406137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree063.table
  base := (-1983947560623054890198385942791488872519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (509894)
      previous := (254947)
      next := (254947)
      square := (1908502517948634309430389079650000000000000)
      linear := (-118048414495629680897434335530102000000000000)
      constant := (1813677036922003669864431709822749637474834849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6150287475123058033/1562500000000000000)
  centralHi := (393618398407875714113/100000000000000000000)
  directionLo := (396780042759664912099/100000000000000000000)
  directionHi := (3967800427596649121/1000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree064.table
  base := (-717927695130526265044957402692719802679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-96872713406913255322345895177026000000000000)
      constant := (1509163418310561459036872042308737898768838605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree064.table
  base := (-1794859819459109787293918969886376220457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-158657977899563413691109559207231971000000000000)
      constant := (2478283454499881643453440674162181226539528521381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396780042759664912099/100000000000000000000)
  centralHi := (3967800427596649121/1000000000000000000)
  directionLo := (399916692699294383379/100000000000000000000)
  directionHi := (19995834634964719169/5000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree065.table
  base := (-3190311872884334498903990372155881541019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-98386897222806386675282402215426000000000000)
      constant := (1557940881638025194899960919303893728420013381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree065.table
  base := (-1595191027415701546558588944496825839193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-161137903421408759554913492508138996000000000000)
      constant := (2558373040143959926073501727298823997455038882069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399916692699294383379/100000000000000000000)
  centralHi := (19995834634964719169/5000000000000000000)
  directionLo := (100757232949650505191/25000000000000000000)
  directionHi := (80605786359720404153/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree066.table
  base := (-2769832262084276669341310904298612250441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-99901081038699518028218909253826000000000000)
      constant := (1607510774390455538982251437963995031986691159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree066.table
  base := (-1384946469985279949959475103932184286153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36015000000000000000000000000000000000000000
      center := (619458)
      previous := (309729)
      next := (309729)
      square := (2318593968086357384184026402550000000000000)
      linear := (-150245940260104779998822245921989000000000000)
      constant := (2424025193131578327830065335329350476586839941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100757232949650505191/25000000000000000000)
  centralHi := (80605786359720404153/20000000000000000000)
  directionLo := (406117321268008144789/100000000000000000000)
  directionHi := (40611732126800814479/10000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree067.table
  base := (-2328208826587885092389357798947889167573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-101415264854592649381155416292226000000000000)
      constant := (1657873074518664130442441483626118118108657227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree067.table
  base := (-232826128020182708567335461636084305013/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-166097754465099451282521359109953046000000000000)
      constant := (2722454604786000246068518661698260985594147960645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406117321268008144789/100000000000000000000)
  centralHi := (40611732126800814479/10000000000000000000)
  directionLo := (204591200569014503579/50000000000000000000)
  directionHi := (409182401138029007159/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree068.table
  base := (-58295293039375422038757349557657562011/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-51464724335242890367045961665313000000000000)
      constant := (854513881634382227728766407137377027097785424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree068.table
  base := (-466373678782644008164552385710357543223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-168577679986944797146325292410860071000000000000)
      constant := (2806446518578306073916999351689680128674006784118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204591200569014503579/50000000000000000000)
  centralHi := (409182401138029007159/100000000000000000000)
  directionLo := (103056172840429366871/25000000000000000000)
  directionHi := (82444938272343493497/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree069.table
  base := (-276312111714507985550819843399315257599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-104443632486378912087028430369026000000000000)
      constant := (1760974824687379534901841194988935220332524005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree069.table
  base := (-1381599740728107479579868105530649797311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (187033246758966162324178129805700000000000000)
      linear := (-12670933741391862445194757460130896000000000000)
      constant := (214202900090354757482711270855956597840235410969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103056172840429366871/25000000000000000000)
  centralHi := (82444938272343493497/20000000000000000000)
  directionLo := (415244692844404171779/100000000000000000000)
  directionHi := (20762234642220208589/5000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree070.table
  base := (-876548023542613063981039260001577125581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (8428)
      previous := (4214)
      next := (4214)
      square := (31545496164440236519510563300000000000000)
      linear := (-2162404414332082519182957906274000000000000)
      constant := (37014576432686024382386578799939922720846531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree070.table
  base := (-35063275250763867843126469891029649631/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (27534276)
      previous := (13767138)
      next := (13767138)
      square := (103059135969226252709241010301100000000000000)
      linear := (-7083164531862673015262577918884658000000000000)
      constant := (121564591063022831132986862222133167514953015675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415244692844404171779/100000000000000000000)
  centralHi := (20762234642220208589/5000000000000000000)
  directionLo := (418242888406514219723/100000000000000000000)
  directionHi := (104560722101628554931/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree071.table
  base := (-70083316455008333301987191622685865811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-107472000118165174792901444445826000000000000)
      constant := (1867246013262409789147870410474665656180938945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree071.table
  base := (-8761145881631339687912624790893639433/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-176017456552480834737737092313581146000000000000)
      constant := (3066226489623396157750610113914440630173274119780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418242888406514219723/100000000000000000000)
  centralHi := (104560722101628554931/25000000000000000000)
  directionLo := (421219743684699860757/100000000000000000000)
  directionHi := (210609871842349930379/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree072.table
  base := (98414835938779992627553206547806999717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-54493091967029153072918975742113000000000000)
      constant := (960785059520811845624888044228057284606320517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree072.table
  base := (196804400641851759592641004845841420583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (187033246758966162324178129805700000000000000)
      linear := (-13222028301801939303817853749221346000000000000)
      constant := (233734900835765739675703581788780430695349193743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421219743684699860757/100000000000000000000)
  centralHi := (210609871842349930379/50000000000000000000)
  directionLo := (53021963497006447761/12500000000000000000)
  directionHi := (424175707976051582089/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree073.table
  base := (191296813784862719745006110154053449007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-55250183874975718749387229261313000000000000)
      constant := (988343277087355673436022654443383764662131614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree073.table
  base := (765165426475588415283522043205553925369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-361954615192343052930689917830790392000000000000)
      constant := (6491832965375122201295762006646895557012707435723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53021963497006447761/12500000000000000000)
  centralHi := (424175707976051582089/100000000000000000000)
  directionLo := (106777803757430355779/25000000000000000000)
  directionHi := (427111215029721423117/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree074.table
  base := (1354653202244319252112097554233301625921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-112014551565844568851710965561026000000000000)
      constant := (2032595311542068341472788989677538157203836321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree074.table
  base := (169329293696037993877764168956557776197/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-183457233118016872329148892216302221000000000000)
      constant := (3337712442492427565637191260394382641143441092796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106777803757430355779/25000000000000000000)
  centralHi := (427111215029721423117/100000000000000000000)
  directionLo := (215013341894953854049/50000000000000000000)
  directionHi := (430026683789907708099/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree075.table
  base := (61413280907456241448140956361260934003/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-56764367690868850102323736299713000000000000)
      constant := (1044648192541600982289341431826174200040659248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree075.table
  base := (393041741730222021454502116309390542869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (149908836)
      previous := (74954418)
      next := (74954418)
      square := (561099740276898486972534389417100000000000000)
      linear := (-41319368586636048487322850114935388000000000000)
      constant := (762402006898723966295171692011817812998572671235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215013341894953854049/50000000000000000000)
  centralHi := (430026683789907708099/100000000000000000000)
  directionLo := (54115314886725575847/12500000000000000000)
  directionHi := (432922519093804606777/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree076.table
  base := (519380093338058029599383034798530637737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-115042919197630831557583979637826000000000000)
      constant := (2146789769638766579018769226267732360306032685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree076.table
  base := (1298443204676728806345108827589577823817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-188417084161707564056756758818116271000000000000)
      constant := (3525206240128860493065511360642443617951734743739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54115314886725575847/12500000000000000000)
  centralHi := (432922519093804606777/100000000000000000000)
  directionLo := (435799112327808620849/100000000000000000000)
  directionHi := (8715982246556172417/2000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree077.table
  base := (3249677805752529076732451182256048514997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (8428)
      previous := (4214)
      next := (4214)
      square := (31545496164440236519510563300000000000000)
      linear := (-2378716388031101283888173197474000000000000)
      constant := (45001540016658372866832050295178546377234853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree077.table
  base := (3249665669387292891509247913677757995289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (227556)
      previous := (113778)
      next := (113778)
      square := (851728396439886386026785209100000000000000)
      linear := (-64394336206292093074906625778048000000000000)
      constant := (1221421508772488462497877723840622923827767347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435799112327808620849/100000000000000000000)
  centralHi := (8715982246556172417/2000000000000000000)
  directionLo := (109664210511248352241/25000000000000000000)
  directionHi := (87731368408998681793/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree078.table
  base := (1961777724298668380088043830178406009007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-59035643414708547131728496857313000000000000)
      constant := (1132076727437909129780621866443122352827625807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree078.table
  base := (490443121494179641325257278214719306073/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-7162108711311046510532023163701123000000000000)
      constant := (137700092332476493269593985376617692870078536132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109664210511248352241/25000000000000000000)
  centralHi := (87731368408998681793/20000000000000000000)
  directionLo := (441496074546610933851/100000000000000000000)
  directionHi := (110374018636652733463/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree079.table
  base := (4618532068960216875866128119898189063871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-119585470645310225616393500753026000000000000)
      constant := (2324023748633079490607958498266579551942354271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree079.table
  base := (115463075653256186567759336174002513609/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-195856860727243601648168558720837346000000000000)
      constant := (3816201525728292377477325630903581699623348156060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441496074546610933851/100000000000000000000)
  centralHi := (110374018636652733463/25000000000000000000)
  directionLo := (444317164430147780921/100000000000000000000)
  directionHi := (222158582215073890461/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree080.table
  base := (2667303268763553191676666454797777120471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-60549827230601678484665003895713000000000000)
      constant := (1192343169688280449127398068101009462866250871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree080.table
  base := (2667299366596450850517693498643203628459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-198336786249088947511972492021744371000000000000)
      constant := (3915801156701087664771654412362993878356275502753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444317164430147780921/100000000000000000000)
  centralHi := (222158582215073890461/50000000000000000000)
  directionLo := (447120455106258051801/100000000000000000000)
  directionHi := (223560227553129025901/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree081.table
  base := (1517944473164197683930170249535998026617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-61306919138548244161133257414913000000000000)
      constant := (1223070612398680963187304439598199862523814834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree081.table
  base := (303588557898554521734675199868476024489/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-7437655991516084939843571308246348000000000000)
      constant := (148766717860277107349895304660361655106105687690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447120455106258051801/100000000000000000000)
  centralHi := (223560227553129025901/50000000000000000000)
  directionLo := (449906279286706181301/100000000000000000000)
  directionHi := (224953139643353090651/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree082.table
  base := (853755664433609586243699937847025339853/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-62064011046494809837601510934113000000000000)
      constant := (1254194201464675375395454566879098831363948212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree082.table
  base := (853754938060996033050565992367515271703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-203296637292779639239580358623558421000000000000)
      constant := (4118902199185627225623584264711878835659046144404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449906279286706181301/100000000000000000000)
  centralHi := (224953139643353090651/50000000000000000000)
  directionLo := (56584369930660291643/12500000000000000000)
  directionHi := (90534991889056466629/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree083.table
  base := (1521881621728707016741750841900145854653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-125642205908882751028139528906626000000000000)
      constant := (2571427872098262461684939366439619250985109265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree083.table
  base := (1521880619047534835770766983553099607823/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-411553125629249970206768583848930892000000000000)
      constant := (8444807209836645925936335390034069649157186680705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56584369930660291643/12500000000000000000)
  centralHi := (90534991889056466629/20000000000000000000)
  directionLo := (227713404126748951973/50000000000000000000)
  directionHi := (455426808253497903947/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree084.table
  base := (8409865678377698161696578338844615375079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (8428)
      previous := (4214)
      next := (4214)
      square := (31545496164440236519510563300000000000000)
      linear := (-2595028361730120048593388488674000000000000)
      constant := (53780808793436242721963683987819386153378871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree084.table
  base := (8409861353555755457921635559656209114493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (3059364)
      previous := (1529682)
      next := (1529682)
      square := (11451015107691805856582334477900000000000000)
      linear := (-944473870006668167651647279933662000000000000)
      constant := (19624515179881504801149422126107562991519486991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227713404126748951973/50000000000000000000)
  centralHi := (455426808253497903947/100000000000000000000)
  directionLo := (229081064496363758301/50000000000000000000)
  directionHi := (458162128992727516603/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree085.table
  base := (9231417519025928136100042816912033614993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-128670573540669013734012542983426000000000000)
      constant := (2699883678055636349736213497842365792709598193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree085.table
  base := (9231413788619100647750090515398909521703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-421472827716631353661984317052558992000000000000)
      constant := (8866616347994498153966319531831388679265176286101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229081064496363758301/50000000000000000000)
  centralHi := (458162128992727516603/100000000000000000000)
  directionLo := (92176243188867060611/20000000000000000000)
  directionHi := (28805075996520956441/6250000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree086.table
  base := (402962528001002124635144271376507881509/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-130184757356562145086949050021826000000000000)
      constant := (2765300012596261655054529975154110885587577725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree086.table
  base := (2014811996536353748591425418597749795541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-426432678760322045389592183654373042000000000000)
      constant := (9081422667560082385690344173892973439227299526235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92176243188867060611/20000000000000000000)
  centralHi := (28805075996520956441/6250000000000000000)
  directionLo := (115896088689801502263/25000000000000000000)
  directionHi := (463584354759206009053/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree087.table
  base := (10937802354761826628207166231752499144839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-131698941172455276439885557060226000000000000)
      constant := (2831508633620013404549916872611349750446758439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree087.table
  base := (10937799580212306195889250573341266582527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (187033246758966162324178129805700000000000000)
      linear := (-15977501103852323596933335194673596000000000000)
      constant := (344401116675395695194214347349538698858822326567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115896088689801502263/25000000000000000000)
  centralHi := (463584354759206009053/100000000000000000000)
  directionLo := (116567955701998596209/25000000000000000000)
  directionHi := (466271822807994384837/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree088.table
  base := (11822634671093942378116300352894152431577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-133213124988348407792822064098626000000000000)
      constant := (2898509540377437920808152610858786859988216377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree088.table
  base := (591131613932419361767092298593652790493/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 324135000000000000000000000000000000000000000
      center := (5575122)
      previous := (2787561)
      next := (2787561)
      square := (20867345712777216457656237622950000000000000)
      linear := (-1803109011767369540681024449826451000000000000)
      constant := (39334044601851170052072287086019945294492897110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116567955701998596209/25000000000000000000)
  centralHi := (466271822807994384837/100000000000000000000)
  directionLo := (117235972378327115507/25000000000000000000)
  directionHi := (468943889513308462029/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree089.table
  base := (12728559883278109469851056188541185673383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-134727308804241539145758571137026000000000000)
      constant := (2966302732230485562388529547841151386801792583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree089.table
  base := (6364278910263631560746873599225557619611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-220656115945697060286207891729907596000000000000)
      constant := (4870724297888712740822069834100843906705589197937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117235972378327115507/25000000000000000000)
  centralHi := (468943889513308462029/100000000000000000000)
  directionLo := (471600816664952771441/100000000000000000000)
  directionHi := (235800408332476385721/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree090.table
  base := (6827788882547867644358664778660828498929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-68120746310067335249347539087713000000000000)
      constant := (1517444104318002744211583569709484649225928529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree090.table
  base := (34138939966966796821017715754019755509/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-8264297832131200227778215741882023000000000000)
      constant := (184567769535290223421397331195253034678046037800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471600816664952771441/100000000000000000000)
  centralHi := (235800408332476385721/50000000000000000000)
  directionLo := (1482008933497736053/312500000000000000)
  directionHi := (474242858719275536961/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree091.table
  base := (456365253874939511104530619836002289079/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (4214)
      previous := (2107)
      next := (2107)
      square := (15772748082220118259755281650000000000000)
      linear := (-1405670167714569406649301889937000000000000)
      constant := (31676183358486613642919364060743425794637936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree091.table
  base := (7301843295530994414623242038879945974469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (13767138)
      previous := (6883569)
      next := (6883569)
      square := (51529567984613126354620505150550000000000000)
      linear := (-4604407489579341877832974659831054000000000000)
      constant := (104025221118070053031192604197953460516430920927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1482008933497736053/312500000000000000)
  centralHi := (474242858719275536961/100000000000000000000)
  directionLo := (238435131541794338993/50000000000000000000)
  directionHi := (476870263083588677987/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree092.table
  base := (3893222699029805201827207684093519579599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-69634930125960466602284046126113000000000000)
      constant := (1587218006662045770095819157591913081021234398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree092.table
  base := (3114577894966042031400458365768366017287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-456191785022466195755239383265257342000000000000)
      constant := (10424884938529540918050135074734926961600611931145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238435131541794338993/50000000000000000000)
  centralHi := (476870263083588677987/100000000000000000000)
  directionLo := (479483270386560432121/100000000000000000000)
  directionHi := (239741635193280216061/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree093.table
  base := (1656318564202821065166837182244617638937/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-70392022033907032278752299645313000000000000)
      constant := (1622699170439220940701369442773030634755438685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree093.table
  base := (16563184503276180394472627494757646430271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (149908836)
      previous := (74954418)
      next := (74954418)
      square := (561099740276898486972534389417100000000000000)
      linear := (-51239070674017431942538583318563488000000000000)
      constant := (1184211040080466638682283184349403973845706283573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479483270386560432121/100000000000000000000)
  centralHi := (239741635193280216061/50000000000000000000)
  directionLo := (96416422947083400241/20000000000000000000)
  directionHi := (241041057367708500603/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree094.table
  base := (8787286271555080047964744894588911755133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-71149113941853597955220553164513000000000000)
      constant := (1658576475754972424331810511498579977124074333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree094.table
  base := (17574571561772056176694616337983202715211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-466111487109847579210455116468885442000000000000)
      constant := (10893514935255693203907841722674818784972697003137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96416422947083400241/20000000000000000000)
  centralHi := (241041057367708500603/50000000000000000000)
  directionLo := (4846670239607313157/1000000000000000000)
  directionHi := (484667023960731315701/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree095.table
  base := (18607051398483408942778892472598450703979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-143812411699600327263377613367426000000000000)
      constant := (3389699844976383575840535513051428880140253579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree095.table
  base := (18607050552879652773880131297947632093329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-471071338153538270938062983070699492000000000000)
      constant := (11131731661359709635973179300857845084881422929043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4846670239607313157/1000000000000000000)
  centralHi := (484667023960731315701/100000000000000000000)
  directionLo := (97447643969904668971/20000000000000000000)
  directionHi := (60904777481190418107/12500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree096.table
  base := (19660622122372976464315727475824848896441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-145326595515493458616314120405826000000000000)
      constant := (3463039021071812334205792409103951462200354841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree096.table
  base := (1966062139379763547279021130366257525329/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-8815392392541277086401312030972473000000000000)
      constant := (210602769229384256058453503630416485512580532045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97447643969904668971/20000000000000000000)
  centralHi := (60904777481190418107/12500000000000000000)
  directionLo := (19591836734693877551/4000000000000000000)
  directionHi := (61224489795918367347/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree097.table
  base := (10367642320936369446300934270126919852613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-73420389665693294984625313722113000000000000)
      constant := (1768585239810591760296286135003910734566123813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree097.table
  base := (20735284014187478986852743703747517364637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-480991040240919654393278716274327592000000000000)
      constant := (11615968565785073672428705556259777782541876058679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19591836734693877551/4000000000000000000)
  centralHi := (61224489795918367347/12500000000000000000)
  directionLo := (492340329869992600287/100000000000000000000)
  directionHi := (15385635308437268759/3125000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree098.table
  base := (21831038895038714566598699115945391985287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (172)
      previous := (86)
      next := (86)
      square := (643785636008984418765521700000000000000)
      linear := (-61788822635268522000077940226000000000000)
      constant := (1504412420023227669734577833163945391985287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree098.table
  base := (10915519177160961869573205604397623288201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (280962)
      previous := (140481)
      next := (140481)
      square := (1051623836420676048053479696950000000000000)
      linear := (-101197603349564836759868093060421000000000000)
      constant := (2470218397144143387326544338809525035282552667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492340329869992600287/100000000000000000000)
  centralHi := (15385635308437268759/3125000000000000000)
  directionLo := (123717914826348378109/25000000000000000000)
  directionHi := (494871659305393512437/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree099.table
  base := (4589576965852881920739051351142180220953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-149869146963172852675123641521026000000000000)
      constant := (3687810243509262485714090810524685873552540765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree099.table
  base := (4589576872701607453715015132534562796543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-150263465665228355631617523562276000000000000)
      constant := (3706951352890241716879478809615920176372498715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123717914826348378109/25000000000000000000)
  centralHi := (494871659305393512437/100000000000000000000)
  directionLo := (3979120851250266299/800000000000000000)
  directionHi := (31086881650392705461/6250000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree100.table
  base := (6021455599974114624385520441443373014299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-75691665389532992014030074279713000000000000)
      constant := (1882159274307224671027967758288611077214663798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree100.table
  base := (12042910999372058280429357751164032035797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-247935296685995864788051158039884871000000000000)
      constant := (6180916272933247431090082589256683970278938066399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3979120851250266299/800000000000000000)
  centralHi := (31086881650392705461/6250000000000000000)
  directionLo := (499895865874117979223/100000000000000000000)
  directionHi := (62486983234264747403/12500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree101.table
  base := (25244851569054991180845050306419514235421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-152897514594959115380996655597826000000000000)
      constant := (3841619135700380636026682304245089253679245821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree101.table
  base := (6311212805893932657427843509991200322449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-250415222207841210651855091340791896000000000000)
      constant := (6307828085361225533121743256019818976104423120166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499895865874117979223/100000000000000000000)
  centralHi := (62486983234264747403/12500000000000000000)
  directionLo := (251194563777370834029/50000000000000000000)
  directionHi := (502389127554741668059/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree102.table
  base := (5284994460925686598708153001653175663053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-154411698410852246733933162636226000000000000)
      constant := (3919712004689956476867518956444398373834951265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree102.table
  base := (26424972007121361658937626090961742408547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (149908836)
      previous := (74954418)
      next := (74954418)
      square := (561099740276898486972534389417100000000000000)
      linear := (-56198921717708123670146449920377538000000000000)
      constant := (1430231216024227956269254519039151615098820448961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251194563777370834029/50000000000000000000)
  centralHi := (502389127554741668059/100000000000000000000)
  directionLo := (504870076606244148957/100000000000000000000)
  directionHi := (252435038303122074479/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree103.table
  base := (2762618457941693444502240414567139672049/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-77962941113372689043434834837313000000000000)
      constant := (1999298577758935012975749247105942511762948245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree103.table
  base := (6906546080810623229981569375796625190643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-255375073251531902379462957942605946000000000000)
      constant := (6565553433074132103109865316286106528863582930162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504870076606244148957/100000000000000000000)
  centralHi := (252435038303122074479/50000000000000000000)
  directionLo := (507338893659430744229/100000000000000000000)
  directionHi := (50733889365943074423/10000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree104.table
  base := (1803030523150153171632263744114262862433/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-78720033021319254719903088356513000000000000)
      constant := (2039137294064427478869907374524498761061613064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree104.table
  base := (28848488149836727571240158211030747106653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-515709997546754496486533782487025942000000000000)
      constant := (13392733936339716183947984857414157387364642277751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507338893659430744229/100000000000000000000)
  centralHi := (50733889365943074423/10000000000000000000)
  directionLo := (254897877485648906361/50000000000000000000)
  directionHi := (509795754971297812723/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree105.table
  base := (15045941829063373171123399743825035206761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (4214)
      previous := (2107)
      next := (2107)
      square := (15772748082220118259755281650000000000000)
      linear := (-1621982141413588171354517181137000000000000)
      constant := (42436166351797878047611552600207426725131289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree105.table
  base := (15045941734117851049533148710018175021501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (509894)
      previous := (254947)
      next := (254947)
      square := (1908502517948634309430389079650000000000000)
      linear := (-196776208839926374986448091114452000000000000)
      constant := (5161361358520775376200056302909079634702479429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254897877485648906361/50000000000000000000)
  centralHi := (509795754971297812723/100000000000000000000)
  directionLo := (256120416285941494279/50000000000000000000)
  directionHi := (512240832571882988559/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree106.table
  base := (1959773151635085732605651530302200509479/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-80234216837212386072839595394913000000000000)
      constant := (2120003149260218295726101031816172667386072632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree106.table
  base := (1959773141418266541143760555743675133493/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-262814849817067939970874757845327021000000000000)
      constant := (6961895760471754438259824733502748256586824288248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256120416285941494279/50000000000000000000)
  centralHi := (512240832571882988559/100000000000000000000)
  directionLo := (514674294404836389029/100000000000000000000)
  directionHi := (51467429440483638903/10000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree107.table
  base := (3264194866065602055544395651336151934791/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-80991308745158951749307848914113000000000000)
      constant := (2161030288114167000301343970112506503977165955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree107.table
  base := (32641948519943692548456814061663858005833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-530589550677826571669357382292468092000000000000)
      constant := (14193222035128294191765861378462647833926240442811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514674294404836389029/100000000000000000000)
  centralHi := (51467429440483638903/10000000000000000000)
  directionLo := (517096304462037847879/100000000000000000000)
  directionHi := (12927407611550946197/2500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree108.table
  base := (33948618349953685943008474519224735333027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-163496801306211034851552204866626000000000000)
      constant := (4404907135571895802549291875147666589534597827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree108.table
  base := (33948618228839684546473595492184450231949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (187033246758966162324178129805700000000000000)
      linear := (-19835163026722861607295009218306746000000000000)
      constant := (535750136930106069677781460689451436665836055429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517096304462037847879/100000000000000000000)
  centralHi := (12927407611550946197/2500000000000000000)
  directionLo := (519507022912565528131/100000000000000000000)
  directionHi := (129876755728141382033/25000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree109.table
  base := (7055275896852549448998049872253630747371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-165010985122104166204488711905026000000000000)
      constant := (4488545976527612316136829524732388837122188855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree109.table
  base := (17638189690012766935006829161359365800759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-270254626382603977562286557748048096000000000000)
      constant := (7369943253411919499178179470683092331043662246853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519507022912565528131/100000000000000000000)
  centralHi := (129876755728141382033/25000000000000000000)
  directionLo := (260953303113151465889/50000000000000000000)
  directionHi := (521906606226302931779/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree110.table
  base := (36625232055377577963689618604958619008897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-166525168937997297557425218943426000000000000)
      constant := (4572977099075781832144323999473865644240361697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree110.table
  base := (9156307991418077393311334244845859928161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 324135000000000000000000000000000000000000000
      center := (5575122)
      previous := (2787561)
      next := (2787561)
      square := (20867345712777216457656237622950000000000000)
      linear := (-2254004561193796061372648686355001000000000000)
      constant := (62054216794214086297756871616663230123125786294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260953303113151465889/50000000000000000000)
  centralHi := (521906606226302931779/100000000000000000000)
  directionLo := (524295207292454245719/100000000000000000000)
  directionHi := (13107380182311356143/2500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree111.table
  base := (18997588028220254033904392788332552942341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-84019676376945214455180862990913000000000000)
      constant := (2329100251599969542413314644779354459614560741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree111.table
  base := (37995175979247085106239622277702766594293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (149908836)
      previous := (74954418)
      next := (74954418)
      square := (561099740276898486972534389417100000000000000)
      linear := (-61158772761398815397754316522191588000000000000)
      constant := (1699661729909947647204309934991944030611221789959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524295207292454245719/100000000000000000000)
  centralHi := (13107380182311356143/2500000000000000000)
  directionLo := (32917060970826377953/6250000000000000000)
  directionHi := (526672975533222047249/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree112.table
  base := (19693105740869516556770557413761109370547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (4214)
      previous := (2107)
      next := (2107)
      square := (15772748082220118259755281650000000000000)
      linear := (-1730138128263097553707124826737000000000000)
      constant := (48410369274350697459328221053818294359156803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree112.table
  base := (19693105707658642004109358845180266204307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (13767138)
      previous := (6883569)
      next := (6883569)
      square := (51529567984613126354620505150550000000000000)
      linear := (-5667232713227347248034660360219779000000000000)
      constant := (158973385936228421703676270248760540554784077481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32917060970826377953/6250000000000000000)
  centralHi := (526672975533222047249/100000000000000000000)
  directionLo := (264520028506443274733/50000000000000000000)
  directionHi := (529040057012886549467/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree113.table
  base := (20399169163266532391866581102670856497109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-85533860192838345808117370029313000000000000)
      constant := (2415512078061844339328723850605456726449558709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree113.table
  base := (10199584567346022743838775867511405508369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-280174328469985361017502290951676196000000000000)
      constant := (7932214610923544690878884859121940164768630993446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264520028506443274733/50000000000000000000)
  centralHi := (529040057012886549467/100000000000000000000)
  directionLo := (132849148635627928949/25000000000000000000)
  directionHi := (531396594542511715797/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree114.table
  base := (21115778293453893140536494232685396156959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-86290952100784911484585623548513000000000000)
      constant := (2459312202451250296313064718621109636172858559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree114.table
  base := (42231556537740624581873995348814218482517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (187033246758966162324178129805700000000000000)
      linear := (-20937352147543015324541201796487646000000000000)
      constant := (598224732201872739369127488215379299567759321357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132849148635627928949/25000000000000000000)
  centralHi := (531396594542511715797/100000000000000000000)
  directionLo := (533742727780490639049/100000000000000000000)
  directionHi := (10674854555609812781/2000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree115.table
  base := (10921466564912082786947984664701175247003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-87048044008731477161053877067713000000000000)
      constant := (2503508467607542599277554165418015043536108406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree115.table
  base := (43685866217351205086450996998820596203829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-570268359027352105490220315106980492000000000000)
      constant := (16442307464536996995304800641562439413852780332543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533742727780490639049/100000000000000000000)
  centralHi := (10674854555609812781/2000000000000000000)
  directionLo := (53607859332913049579/10000000000000000000)
  directionHi := (536078593329130495791/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree116.table
  base := (22580633671066531190980515779376578557747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-87805135916678042837522130586913000000000000)
      constant := (2548100873527573973001376449033291165117150547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree116.table
  base := (9032253461149718698034292949784394080189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-575228210071042797217828181708794542000000000000)
      constant := (16735148307087035290760345705247905335597029443315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53607859332913049579/10000000000000000000)
  centralHi := (536078593329130495791/100000000000000000000)
  directionLo := (538404324827466088609/100000000000000000000)
  directionHi := (53840432482746608861/10000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree117.table
  base := (46657759832242704517419543958888136422953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-177124455649249217027980768212226000000000000)
      constant := (5186178840417600454574811242515482415551510153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree117.table
  base := (9331551960189308068484570449821062288643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (49969612)
      previous := (24984806)
      next := (24984806)
      square := (187033246758966162324178129805700000000000000)
      linear := (-21488446707953092183164298085578096000000000000)
      constant := (630762603595744391687546643268945599935794265015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538404324827466088609/100000000000000000000)
  centralHi := (53840432482746608861/10000000000000000000)
  directionLo := (540720053040480419679/100000000000000000000)
  directionHi := (3379500331503002623/625000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree118.table
  base := (24087671864141493420521731980062282425939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-89319319732571174190458637625313000000000000)
      constant := (2638474107649187390144536305806513540104679539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree118.table
  base := (24087671850682688323400886891759816666691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-292573956079212090336521957456211321000000000000)
      constant := (8664316717259397910134715357010669452841240872297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540720053040480419679/100000000000000000000)
  centralHi := (3379500331503002623/625000000000000000)
  directionLo := (3393911912155630287/625000000000000000)
  directionHi := (543025905944900845921/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree119.table
  base := (4971401902891880153663904097820274859469/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (4214)
      previous := (2107)
      next := (2107)
      square := (15772748082220118259755281650000000000000)
      linear := (-1838294115112606936059732472337000000000000)
      constant := (54780712976472095196723018471493967340569905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree119.table
  base := (24857009502884357378166404396120808204303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (13767138)
      previous := (6883569)
      next := (6883569)
      square := (51529567984613126354620505150550000000000000)
      linear := (-6021507787776682371435222260349354000000000000)
      constant := (179890588973249272625882777513286861464769437149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3393911912155630287/625000000000000000)
  centralHi := (543025905944900845921/100000000000000000000)
  directionLo := (545322008811730100521/100000000000000000000)
  directionHi := (272661004405865050261/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree120.table
  base := (10254757146623635025341774620769942174567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-181667007096928611086790289327426000000000000)
      constant := (5460863809602794333224689576311463155805676835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree120.table
  base := (51273785713209613012565083386235736018631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (149908836)
      previous := (74954418)
      next := (74954418)
      square := (561099740276898486972534389417100000000000000)
      linear := (-66118623805089507125362183124005638000000000000)
      constant := (1992502572406285488105669338234411836791606090253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545322008811730100521/100000000000000000000)
  centralHi := (272661004405865050261/50000000000000000000)
  directionLo := (273804242142831391397/50000000000000000000)
  directionHi := (109521696857132556559/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree121.table
  base := (52854643840104602676646549078345221261113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-183181190912821742439726796365826000000000000)
      constant := (5554010029022097403778583916496002876247932313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree121.table
  base := (52854643822984801438563097458832550831929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (11150244)
      previous := (5575122)
      next := (5575122)
      square := (41734691425554432915312475245900000000000000)
      linear := (-4958904671814018643436921609238552000000000000)
      constant := (150730328358245465704915667272139661022781461283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273804242142831391397/50000000000000000000)
  centralHi := (109521696857132556559/20000000000000000000)
  directionLo := (274942726230764888573/50000000000000000000)
  directionHi := (549885452461529777147/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree122.table
  base := (27228296674658254129009834956196057876039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-92347687364357436896331651702113000000000000)
      constant := (2823974264975413098568186320393362734960369639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree122.table
  base := (85088427085305895797556388787236452971/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-302493658166593473791737690659839421000000000000)
      constant := (9273408729223957134612838822245032386222999378240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274942726230764888573/50000000000000000000)
  centralHi := (549885452461529777147/100000000000000000000)
  directionLo := (134802986073707379/24414062500000000)
  directionHi := (110430606191581084877/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree123.table
  base := (28039817130186388807183111359407280614437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-93104779272304002572799905221313000000000000)
      constant := (2871339656194032828984145228120760880755263237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree123.table
  base := (28039817123857862122211600465184139742337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-11295317914386622950205245331879498000000000000)
      constant := (349219746906567493967806590500571099837083487577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134802986073707379/24414062500000000)
  centralHi := (110430606191581084877/20000000000000000000)
  directionLo := (277205667494002549793/50000000000000000000)
  directionHi := (554411334988005099587/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree124.table
  base := (57723766573043464499850987921695542081971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-187723742360501136498536317481026000000000000)
      constant := (5838202376333263685338087000658614996538812371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree124.table
  base := (14430941640540367773304530994943132376737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-307453509210284165519345557261653471000000000000)
      constant := (9585758177433227832260844451983846012105988538758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277205667494002549793/50000000000000000000)
  centralHi := (554411334988005099587/100000000000000000000)
  directionLo := (556660477427994118071/100000000000000000000)
  directionHi := (69582559678499264759/12500000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree125.table
  base := (59388990287224904743522706697066374958851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-189237926176394267851472824519426000000000000)
      constant := (5934517721786171381571308301601656366276201251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree125.table
  base := (59388990277869611318462160024996686568309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-619866869464259022766298981125120992000000000000)
      constant := (19487767524182849906247220998571220465469815872703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556660477427994118071/100000000000000000000)
  centralHi := (69582559678499264759/12500000000000000000)
  directionLo := (34931285555176410297/6250000000000000000)
  directionHi := (558900568882822564753/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree126.table
  base := (61075305402918585117228237541973471780721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (8428)
      previous := (4214)
      next := (4214)
      square := (31545496164440236519510563300000000000000)
      linear := (-3892900203924232636824680235874000000000000)
      constant := (123094394872383516661370585026980700117255329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree126.table
  base := (12215061078975258578875970304805121606229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (1019788)
      previous := (509894)
      next := (509894)
      square := (3817005035897268618860778159300000000000000)
      linear := (-472280212024149444061909937813254000000000000)
      constant := (14970990053593432310332489610677401830016658705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34931285555176410297/6250000000000000000)
  centralHi := (558900568882822564753/100000000000000000000)
  directionLo := (140282929437423673671/25000000000000000000)
  directionHi := (112226343549938938937/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree127.table
  base := (15695677980053302610040772268955293768141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-96133146904090265278672919298113000000000000)
      constant := (3064762628607669735058263255507499320674613082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree127.table
  base := (12556542382660011601960199464362824392003/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-629786571551640406221514714328749092000000000000)
      constant := (20128073305031168638361184766768986774450528981005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140282929437423673671/25000000000000000000)
  centralHi := (112226343549938938937/20000000000000000000)
  directionLo := (563354030279275958597/100000000000000000000)
  directionHi := (281677015139637979299/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree128.table
  base := (64511209839269494497655514117115822360681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-193780477624073661910282345634626000000000000)
      constant := (6228217447192198716497984970697723089487995081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree128.table
  base := (12902241966665460653101075213469397799437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-634746422595331097949122580930563142000000000000)
      constant := (20452127916565485089046212870067378869942181951395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563354030279275958597/100000000000000000000)
  centralHi := (281677015139637979299/50000000000000000000)
  directionLo := (17673987832335482587/3125000000000000000)
  directionHi := (113113522126947088557/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree129.table
  base := (66260799160307270382734827131198493057731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-195294661439966793263218852673026000000000000)
      constant := (6327701918677897874807897429401511581831612131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree129.table
  base := (16565199788799991687421034318134973703403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (74954418)
      previous := (37477209)
      next := (37477209)
      square := (280549870138449243486267194708550000000000000)
      linear := (-35539237424390099426485024862909844000000000000)
      constant := (1154376870861608782066588408355547935796718057778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17673987832335482587/3125000000000000000)
  centralHi := (113113522126947088557/20000000000000000000)
  directionLo := (141943140237179139069/25000000000000000000)
  directionHi := (567772560948716556277/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree130.table
  base := (17007869970898643893325008038591161238707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-98404422627929962308077679855713000000000000)
      constant := (3213989335836540251515349697908754756268271014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree130.table
  base := (34015739939602555026601056467672603376729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-322333062341356240702169157067095621000000000000)
      constant := (10554020290931919666585095268951060464951488516843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141943140237179139069/25000000000000000000)
  centralHi := (567772560948716556277/100000000000000000000)
  directionLo := (569968981378324129383/100000000000000000000)
  directionHi := (71246122672290516173/12500000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree131.table
  base := (69823252009438417958400621788639259452227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-198323029071753055969091866749826000000000000)
      constant := (6529047706178483727107998701683178861944797027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree131.table
  base := (6982325200566611243802678789709851566877/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-324812987863201586565973090368002646000000000000)
      constant := (10719949317816332732779146967745536935378190843795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569968981378324129383/100000000000000000000)
  centralHi := (71246122672290516173/12500000000000000000)
  directionLo := (114431394031642337533/20000000000000000000)
  directionHi := (286078485079105843833/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree132.table
  base := (35818057769088486211271596949310817920991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-99918606443823093661014186894113000000000000)
      constant := (3315454511097459752468747844235711273828299391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree132.table
  base := (71636115534935236257424088536220153335347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-200362971157053524597353549843226000000000000)
      constant := (6664939650082093554901590798437746588158168147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114431394031642337533/20000000000000000000)
  centralHi := (286078485079105843833/50000000000000000000)
  directionLo := (114867324730369703377/20000000000000000000)
  directionHi := (287168311825924258443/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree133.table
  base := (73470070470172994593714471642050590636289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (8428)
      previous := (4214)
      next := (4214)
      square := (31545496164440236519510563300000000000000)
      linear := (-4109212177623251401529895527074000000000000)
      constant := (137419645300474669648611968948652478941178161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree133.table
  base := (73470070467387358419526629107109257721641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (27534276)
      previous := (13767138)
      next := (13767138)
      square := (103059135969226252709241010301100000000000000)
      linear := (-13460115873750705236472692121217008000000000000)
      constant := (451253432355579233217753984041100316553853456203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114867324730369703377/20000000000000000000)
  centralHi := (287168311825924258443/50000000000000000000)
  directionLo := (576508036401042221187/100000000000000000000)
  directionHi := (144127009100260555297/25000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree134.table
  base := (75325116805808269902339576762559679671979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-202865580519432450027901387865026000000000000)
      constant := (6837008498764418317459921789027289790892421579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree134.table
  base := (1506502336068293862039314722843057235043/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-332252764428737624157384890270723721000000000000)
      constant := (11225539840725645185632664100331693824912800997025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576508036401042221187/100000000000000000000)
  centralHi := (144127009100260555297/25000000000000000000)
  directionLo := (289335650586894391897/50000000000000000000)
  directionHi := (115734260234757756759/20000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree135.table
  base := (38600627272739471494439709216777410143013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-102189882167662790690418947451713000000000000)
      constant := (3470623329659674581126524131513362561753374213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree135.table
  base := (19300313635855589211089578444080136172997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-12397507035206776667451437910060398000000000000)
      constant := (422098931942687059924614985866885424857230522874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289335650586894391897/50000000000000000000)
  centralHi := (115734260234757756759/20000000000000000000)
  directionLo := (36301656813157415801/6250000000000000000)
  directionHi := (580826509010518652817/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree136.table
  base := (39549241844795797711400614694110083362251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-102946974075609356366887200970913000000000000)
      constant := (3523138550694513774754828363137326310152764651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree136.table
  base := (79098483687824649232155657442392046518563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-674425230944856631769985513745075542000000000000)
      constant := (23138206115788064815367940513070709665158724915721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36301656813157415801/6250000000000000000)
  centralHi := (580826509010518652817/100000000000000000000)
  directionLo := (582973749268804081469/100000000000000000000)
  directionHi := (58297374926880408147/10000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree137.table
  base := (40508402119279979619857719451964657259267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-103704065983555922043355454490113000000000000)
      constant := (3576049912487223424923623909733023142079500067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree137.table
  base := (10127100529630242650754341381814189442713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-339692540994273661748796690173444796000000000000)
      constant := (11742835527051739263702522579869611226782333735084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582973749268804081469/100000000000000000000)
  centralHi := (58297374926880408147/10000000000000000000)
  directionLo := (585113109666589839977/100000000000000000000)
  directionHi := (292556554833294919989/50000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree138.table
  base := (41478108096401085232431931885181754122771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-104461157891502487719823708009313000000000000)
      constant := (3629357415038305503931213572356465391648773171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree138.table
  base := (82956216191498079068264528939339968264011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (149908836)
      previous := (74954418)
      next := (74954418)
      square := (561099740276898486972534389417100000000000000)
      linear := (-76038325892470890580577916327633738000000000000)
      constant := (2648415237761629672314802602259805904760086219193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (585113109666589839977/100000000000000000000)
  centralHi := (292556554833294919989/50000000000000000000)
  directionLo := (587244676324006474481/100000000000000000000)
  directionHi := (293622338162003237241/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree139.table
  base := (3396668782109539239788374259337163999851/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-210436499598898106792583923057026000000000000)
      constant := (7366122116696529048358602010857977269091056275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree139.table
  base := (42458359775809112961299060923747546465871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-344652392037964353476404556775258846000000000000)
      constant := (12094202186522482696762121166645717117688905337357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587244676324006474481/100000000000000000000)
  centralHi := (293622338162003237241/50000000000000000000)
  directionLo := (589368533803822505943/100000000000000000000)
  directionHi := (73671066725477813243/12500000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree140.table
  base := (21724578579697339829083117595166319112857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (4214)
      previous := (2107)
      next := (2107)
      square := (15772748082220118259755281650000000000000)
      linear := (-2162762075661135083117555409137000000000000)
      constant := (76268588620767454246665845168006299273059986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree140.table
  base := (86898314317827073927729639224638116872691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (27534276)
      previous := (13767138)
      next := (13767138)
      square := (103059135969226252709241010301100000000000000)
      linear := (-14168666022849375483273815921476158000000000000)
      constant := (500891280687300099371944352703616113663330993353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589368533803822505943/100000000000000000000)
  centralHi := (73671066725477813243/12500000000000000000)
  directionLo := (591484765150589329539/100000000000000000000)
  directionHi := (29574238257529466477/5000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree141.table
  base := (44450500245686960432758429581743315488633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-106732433615342184749228468566913000000000000)
      constant := (3791656767246830853733848072034973700488207833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree141.table
  base := (1778020009810947413298517020910859870243/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-12948601595616853526074534199150848000000000000)
      constant := (461139671884374102560886310304652487884071665075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591484765150589329539/100000000000000000000)
  centralHi := (29574238257529466477/5000000000000000000)
  directionLo := (148398362982132520839/25000000000000000000)
  directionHi := (593593451928530083357/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree142.table
  base := (90924778070908637622119613208557376211667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-214979051046577500851393444172226000000000000)
      constant := (7693097665672882571465568837668338260284212467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree142.table
  base := (45462389035099355686334854584952042895551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-352092168603500391067816356677979921000000000000)
      constant := (12631006478641873366937773003979392873259576045917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148398362982132520839/25000000000000000000)
  centralHi := (593593451928530083357/100000000000000000000)
  directionLo := (595694674258221395809/100000000000000000000)
  directionHi := (59569467425822139581/10000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree143.table
  base := (23242411764451571010022860224725081511879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-108246617431235316102164975605313000000000000)
      constant := (3901837039186932089815403279043713841420042958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree143.table
  base := (3718785882287862240080116742820173170409/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (11150244)
      previous := (5575122)
      next := (5575122)
      square := (41734691425554432915312475245900000000000000)
      linear := (-5860695770666871684820170082295652000000000000)
      constant := (211777560167467763237025759426451126402952606075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595694674258221395809/100000000000000000000)
  centralHi := (59569467425822139581/10000000000000000000)
  directionLo := (597788510852114686227/100000000000000000000)
  directionHi := (149447127713028671557/25000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree144.table
  base := (47517803726237541400384538196904197515853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-109003709339181881778633229124513000000000000)
      constant := (3957521386298793337310649402021838978235563053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree144.table
  base := (18561642080459264879031105351558482693/1953125000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-13224148875821891955386082343696073000000000000)
      constant := (481310328716647770912869988013281124193159815680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597788510852114686227/100000000000000000000)
  centralHi := (149447127713028671557/25000000000000000000)
  directionLo := (149968759762235393767/25000000000000000000)
  directionHi := (599875039048941575069/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree145.table
  base := (97122659255318019325038400830971549035197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-219521602494256894910202965287426000000000000)
      constant := (8027203748345017624432592576148682689233507997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree145.table
  base := (48561329627434161199719069620448979969169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-359531945169036428659228156580700996000000000000)
      constant := (13179515934296532091191728737483272429584819570323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149968759762235393767/25000000000000000000)
  centralHi := (599875039048941575069/100000000000000000000)
  directionLo := (300977167423522976211/50000000000000000000)
  directionHi := (601954334847045952423/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree146.table
  base := (24807700616683074655460859076506343830683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-110517893155075013131569736162913000000000000)
      constant := (4070078502808555359145581235727031463074939766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree146.table
  base := (99230802466346126185798080025623029593413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-724023741381763549046064179763216042000000000000)
      constant := (26729907133948982099693537599087104492873714330671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300977167423522976211/50000000000000000000)
  centralHi := (601954334847045952423/100000000000000000000)
  directionLo := (151006618234170837317/25000000000000000000)
  directionHi := (604026472936683349269/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree147.table
  base := (101360037087108922005971777801875367260099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (172)
      previous := (86)
      next := (86)
      square := (643785636008984418765521700000000000000)
      linear := (-92690533163699774100822981826000000000000)
      constant := (3437693687802917430384761976473875367260099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree147.table
  base := (101360037086777315819432750906752535790633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (62436)
      previous := (31218)
      next := (31218)
      square := (233694185871261344011884377100000000000000)
      linear := (-33735184063374253356179001636588000000000000)
      constant := (1254263665452811880638005853428093420491999779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151006618234170837317/25000000000000000000)
  centralHi := (604026472936683349269/100000000000000000000)
  directionLo := (303045763365663224743/50000000000000000000)
  directionHi := (606091526731326449487/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree148.table
  base := (103510363116832364588276392930163082223211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-224064153941936288969012486402626000000000000)
      constant := (8368440364739022845361703653563369560417929611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree148.table
  base := (25877590779136906843599815451168387780193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-366971721734572466250639956483422071000000000000)
      constant := (13739730553529289704516035534965062207059630329862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303045763365663224743/50000000000000000000)
  centralHi := (606091526731326449487/100000000000000000000)
  directionLo := (121629913679602773219/20000000000000000000)
  directionHi := (38009348024875866631/6250000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree149.table
  base := (10568178055628033731278562696972256807027/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-112789168878914710160974496720513000000000000)
      constant := (4241885233295335943645722486308663942968359135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree149.table
  base := (52840890278017927810160343529882553699927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-369451647256417812114443889784329096000000000000)
      constant := (13929069907409127916110959154283189747978325283109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121629913679602773219/20000000000000000000)
  centralHi := (38009348024875866631/6250000000000000000)
  directionLo := (61020066888677767749/10000000000000000000)
  directionHi := (610200668886777677491/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree150.table
  base := (107874289405823619761085135796432983682131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-227092521573722551674885500479426000000000000)
      constant := (8599892849970642117918424622433635593820796531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree150.table
  base := (53937144702806855828180249773104420876719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-13775243436231968814009178632786523000000000000)
      constant := (522952216112069572685975780144707394457525280599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61020066888677767749/10000000000000000000)
  centralHi := (610200668886777677491/100000000000000000000)
  directionLo := (612244897959183673469/100000000000000000000)
  directionHi := (61224489795918367347/10000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree151.table
  base := (13760986208228244003458326560937848660271/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-114303352694807841513911003758913000000000000)
      constant := (4358403757439903438604758579045335098533242684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree151.table
  base := (55043944832822868072037994486154675504769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-374411498300108503842051756386143146000000000000)
      constant := (14311650336380971084433936116241967771147666855523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (612244897959183673469/100000000000000000000)
  centralHi := (61224489795918367347/10000000000000000000)
  directionLo := (307141162108008396043/50000000000000000000)
  directionHi := (614282324216016792087/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree152.table
  base := (56161290668321987872062742212141528837447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-115060444602754407190379257278113000000000000)
      constant := (4417257230659511230861091600365527810738710247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree152.table
  base := (112322581336489258701288243155322973386111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-753782847643907699411711379374100342000000000000)
      constant := (29009782822951614481160731629427030693879871553437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307141162108008396043/50000000000000000000)
  centralHi := (614282324216016792087/100000000000000000000)
  directionLo := (616313015124142832427/100000000000000000000)
  directionHi := (154078253781035708107/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree153.table
  base := (22915672883725443168153924018330917195423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-231635073021401945733695021594626000000000000)
      constant := (8953013689289128080814091942586990660931053115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree153.table
  base := (28644591104623598865610179640733379382201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-14050790716437007243320726777331748000000000000)
      constant := (544423446678213336969215292571992220097992833442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616313015124142832427/100000000000000000000)
  centralHi := (154078253781035708107/25000000000000000000)
  directionLo := (309168518521288100613/50000000000000000000)
  directionHi := (618337037042576201227/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree154.table
  base := (116855238912118095920269497026812334157313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (8428)
      previous := (4214)
      next := (4214)
      square := (31545496164440236519510563300000000000000)
      linear := (-4758148098720307695645541400674000000000000)
      constant := (185149085689611140684801126535209804373708337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree154.table
  base := (116855238912004078038977474041618630673599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (227556)
      previous := (113778)
      next := (113778)
      square := (851728396439886386026785209100000000000000)
      linear := (-128807986124353024602281516710698000000000000)
      constant := (5024548923221512783426402412752453448381171477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309168518521288100613/50000000000000000000)
  centralHi := (618337037042576201227/100000000000000000000)
  directionLo := (620354455247782189047/100000000000000000000)
  directionHi := (77544306905972773631/12500000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree155.table
  base := (59576602408725990606301406822605986425811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-117331720326594104219784017835713000000000000)
      constant := (4596194494912640555931424713770716973408372211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree155.table
  base := (119153204817354108157931642736899339914403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-768662400774979774594534979179542492000000000000)
      constant := (30184836158424735822198837556005568210794351397001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620354455247782189047/100000000000000000000)
  centralHi := (77544306905972773631/12500000000000000000)
  directionLo := (62236533395824107089/10000000000000000000)
  directionHi := (622365333958241070891/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree156.table
  base := (30368065533739311003000539204697619764351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-118088812234540669896252271354913000000000000)
      constant := (4656632531196461078807663532807485970108413502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree156.table
  base := (121472262134873233145341408587477931726573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (149908836)
      previous := (74954418)
      next := (74954418)
      square := (561099740276898486972534389417100000000000000)
      linear := (-85958027979852274035793649531261838000000000000)
      constant := (3397969210951028722242248123405544406609407143599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62236533395824107089/10000000000000000000)
  centralHi := (622365333958241070891/100000000000000000000)
  directionLo := (156092434089575045817/25000000000000000000)
  directionHi := (624369736358300183269/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree157.table
  base := (123812410864955347289014896922095305366323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-237691808284974471145441049748226000000000000)
      constant := (9434933416494640863404972350715182828184541523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree157.table
  base := (30953102716220809544114345985217037777683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-389291051431180579024875356191585296000000000000)
      constant := (15490605393093220715676799557093607970364353113522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156092434089575045817/25000000000000000000)
  centralHi := (624369736358300183269/100000000000000000000)
  directionLo := (626367724621339041839/100000000000000000000)
  directionHi := (7829596557766738023/1250000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree158.table
  base := (63086825503880471422344283868598492017317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-119602996050433801249188778393313000000000000)
      constant := (4778697026065596354103050205726408979333578117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree158.table
  base := (15771706375962381482087940219632265116837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-391770976953025924888679289492492321000000000000)
      constant := (15691649910654377468400048808520256104752929024316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626367724621339041839/100000000000000000000)
  centralHi := (7829596557766738023/1250000000000000000)
  directionLo := (628359359932271527589/100000000000000000000)
  directionHi := (62835935993227152759/10000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree159.table
  base := (32138995640920495236707727239565425422681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-120360087958380366925657031912513000000000000)
      constant := (4840323484651658540305858815416785172879714162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree159.table
  base := (2571119651272577244856378874213809616609/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-14601885276847084101943823066422198000000000000)
      constant := (588666481554233638227507223910126620965671582225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628359359932271527589/100000000000000000000)
  centralHi := (62835935993227152759/10000000000000000000)
  directionLo := (630344702509408182599/100000000000000000000)
  directionHi := (3151723512547040913/500000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree160.table
  base := (32739851383254957218801478659910218184493/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-121117179866326932602125285431713000000000000)
      constant := (4902346084005868781730268679290968867721935386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree160.table
  base := (65479702766487120438435097459893035495823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-396730827996716616616287156094306371000000000000)
      constant := (16097640667024195780595369917435235143262613832141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630344702509408182599/100000000000000000000)
  centralHi := (3151723512547040913/500000000000000000)
  directionLo := (632323811625700715947/100000000000000000000)
  directionHi := (158080952906425178987/25000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree161.table
  base := (133383919916069396216156657150856581397449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (8428)
      previous := (4214)
      next := (4214)
      square := (31545496164440236519510563300000000000000)
      linear := (-4974460072419326460350756691874000000000000)
      constant := (202643462209329841523864679825655972488475001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree161.table
  base := (133383919916030272799093769754183976915473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (27534276)
      previous := (13767138)
      next := (13767138)
      square := (103059135969226252709241010301100000000000000)
      linear := (-16294316470145386223677187322253608000000000000)
      constant := (665411710442252957027397134814154102826559664259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (632323811625700715947/100000000000000000000)
  centralHi := (158080952906425178987/25000000000000000000)
  directionLo := (634296745629389923817/100000000000000000000)
  directionHi := (317148372814694961909/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree162.table
  base := (6791476285655963254917717574518424132983/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-122631363682220063955061792470113000000000000)
      constant := (5027579705020141989964576538335243363432921830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree162.table
  base := (339573814282714227098031965366345091299/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (24984806)
      previous := (12492403)
      next := (12492403)
      square := (93516623379483081162089064902850000000000000)
      linear := (-14877432557052122531255371210967423000000000000)
      constant := (611438285866609098211148095050531814453855355800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (634296745629389923817/100000000000000000000)
  centralHi := (317148372814694961909/50000000000000000000)
  directionLo := (159065890491019343283/25000000000000000000)
  directionHi := (636263561964077373133/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree163.table
  base := (138296222924451823859420867084128051978533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-246776911180333259263060091978626000000000000)
      constant := (10181581453361780813638518762713679452800457733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree163.table
  base := (138296222924423012768835790905725662836807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-808341209124505308415397911994054892000000000000)
      constant := (33432762209430096876698540554317441735161324174069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159065890491019343283/25000000000000000000)
  centralHi := (636263561964077373133/100000000000000000000)
  directionLo := (319112158594120191379/50000000000000000000)
  directionHi := (638224317188240382759/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree164.table
  base := (35196002887585850721488060026643169803129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-124145547498113195307998299508513000000000000)
      constant := (5154397889111158102527841726220772501394625458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree164.table
  base := (140784011550318680137344425010732005853977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-813301060168196000143005778595868942000000000000)
      constant := (33850458129572180040267023271068827410962987804459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319112158594120191379/50000000000000000000)
  centralHi := (638224317188240382759/100000000000000000000)
  directionLo := (320089533497104529269/50000000000000000000)
  directionHi := (640179066994209058539/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree165.table
  base := (143292891591064411583712126060946949045823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-249805278812119521968933106055426000000000000)
      constant := (10436802384622539407163885682717373624659021023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree165.table
  base := (8955805724440199863546652136989584012259/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36015000000000000000000000000000000000000000
      center := (619458)
      previous := (309729)
      next := (309729)
      square := (2318593968086357384184026402550000000000000)
      linear := (-375693714973318040344634364186264000000000000)
      constant := (15734965655291672475871120507350838414122412616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320089533497104529269/50000000000000000000)
  centralHi := (640179066994209058539/100000000000000000000)
  directionLo := (642127866226623396117/100000000000000000000)
  directionHi := (321063933113311698059/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree166.table
  base := (145822863046879475616201667284897642672877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-251319462628012653321869613093826000000000000)
      constant := (10565601272563085786181191696293855240057577677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree166.table
  base := (145822863046861273452794763732812408287809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (1349179524)
      previous := (674589762)
      next := (674589762)
      square := (5049897662492086382752809504753900000000000000)
      linear := (-823220762255577383598221511799497042000000000000)
      constant := (34693653412391421097748070504394663451040929079203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642127866226623396117/100000000000000000000)
  centralHi := (321063933113311698059/50000000000000000000)
  directionLo := (12881415378007755139/2000000000000000000)
  directionHi := (644070768900387756951/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree167.table
  base := (4636685184938986678229183315862215317089/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (206486)
      previous := (103243)
      next := (103243)
      square := (772864656028785794728008800850000000000000)
      linear := (-126416823221952892337403060066113000000000000)
      constant := (5347596221022288575007056305881658863621291024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree167.table
  base := (74186962959015978082461703769663522093651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-414090306649634037662914689200655546000000000000)
      constant := (17559576387536343687409232319748005694883578718617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12881415378007755139/2000000000000000000)
  centralHi := (644070768900387756951/100000000000000000000)
  directionLo := (646007828218139346231/100000000000000000000)
  directionHi := (80750978527267418279/12500000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree168.table
  base := (75473040102411086700856005160219205118999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (4214)
      previous := (2107)
      next := (2107)
      square := (15772748082220118259755281650000000000000)
      linear := (-2595386023059172612527985991537000000000000)
      constant := (110465060133343082390469927786866741050830951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree168.table
  base := (150946080204808773960205349058355544775373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (1019788)
      previous := (509894)
      next := (509894)
      square := (3817005035897268618860778159300000000000000)
      linear := (-629735800712742832239937448981954000000000000)
      constant := (26868672173296334220961708107605562024973186517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell056.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (646007828218139346231/100000000000000000000)
  centralHi := (80750978527267418279/12500000000000000000)
  directionLo := (80992387073405834403/12500000000000000000)
  directionHi := (25917563863489867009/4000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree169.table
  base := (153539325907451365397582768023439632791891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (412972)
      previous := (206486)
      next := (206486)
      square := (1545729312057571589456017601700000000000000)
      linear := (-255862014075692047380679134209026000000000000)
      constant := (10956751625632816224674690880450822558333330291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree169.table
  base := (76769662953719934714993155528825654399949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (674589762)
      previous := (337294881)
      next := (337294881)
      square := (2524948831246043191376404752376950000000000000)
      linear := (-419050157693324729390522555802469596000000000000)
      constant := (17988977471494227971700882767273394029057044752583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell056.Kernel169
