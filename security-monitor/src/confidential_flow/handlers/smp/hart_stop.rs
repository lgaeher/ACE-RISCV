// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiRequest;
use crate::confidential_flow::{ConfidentialFlow, DeclassifyToHypervisor};
use crate::core::control_data::ConfidentialHart;

/// Handles a request to stops the confidential hart as defined in the HSM extension of SBI. Error is returned to the confidential hart if
/// the security monitor cannot stop it, for example, because it is not in the started state.
///
/// The request to stop the confidential hart comes from the confidential hart itself. The security monitor stops the
/// hart and informs the hypervisor that the hart has been stopped. The hypervisor should not resume execution of a
/// stopped confidential hart. Only another confidential hart of the confidential VM can start the confidential hart.
pub struct SbiHsmHartStop {}

impl SbiHsmHartStop {
    pub fn from_confidential_hart(_confidential_hart: &ConfidentialHart) -> Self {
        Self {}
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        match confidential_flow.stop_confidential_hart() {
            Ok(_) => confidential_flow
                .into_non_confidential_flow()
                .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(SbiRequest::kvm_hsm_hart_stop())),
            Err(error) => confidential_flow.apply_and_exit_to_confidential_hart(error.into_confidential_transformation()),
        }
    }
}