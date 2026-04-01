use crate::libraries::utils::SmtOption;

pub mod constrains;
pub mod publication;
pub mod unfold;

static SMT_OPTIONS: SmtOption = SmtOption {
    depend_on_context: false,
};
