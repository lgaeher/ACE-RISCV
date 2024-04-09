// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::handlers::smp::SbiIpi;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, InterHartRequest, InterHartRequestExecutable};

/// Handles a request from one confidential hart to execute sfence.vma instruction on remote confidential harts. It represents an inter hart
/// request.
#[derive(Clone)]
pub struct SbiRemoteSfenceVmaAsid {
    ipi: SbiIpi,
    _start_address: usize,
    _size: usize,
    _asid: usize,
}

impl SbiRemoteSfenceVmaAsid {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let ipi = SbiIpi::from_confidential_hart(confidential_hart);
        let _start_address = confidential_hart.gprs().read(GeneralPurposeRegister::a2);
        let _size = confidential_hart.gprs().read(GeneralPurposeRegister::a3);
        let _asid = confidential_hart.gprs().read(GeneralPurposeRegister::a4);
        Self { ipi, _start_address, _size, _asid }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        let transformation = confidential_flow
            .broadcast_inter_hart_request(InterHartRequest::SbiRemoteSfenceVmaAsid(self))
            .and_then(|_| Ok(ApplyToConfidentialHart::SbiResponse(SbiResponse::success(0))))
            .unwrap_or_else(|error| error.into_confidential_transformation());
        confidential_flow.apply_and_exit_to_confidential_hart(transformation)
    }
}

impl InterHartRequestExecutable for SbiRemoteSfenceVmaAsid {
    fn execute_on_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        // TODO: execute a more fine grained fence. Right now, we just clear all tlbs
        crate::core::architecture::hfence_vvma();
        self.ipi.execute_on_confidential_hart(confidential_hart);
    }

    fn is_hart_selected(&self, hart_id: usize) -> bool {
        self.ipi.is_hart_selected(hart_id)
    }
}