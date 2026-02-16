use super::{Perhaps, PerhapsCast, PerhapsKind, Wrap};

/// The kind of `Perhaps<T>` that represents a value that exists. This is
/// guaranteed by the compiler to have the same size and memory layout as `T`
/// itself.
#[repr(transparent)]
pub struct Always<T: Send>(T);

impl PerhapsKind for Always<()> {
    type Rebind<T: Send> = Always<T>;

    fn empty<T: Send>() -> Wrap<Self, T> {
        // See the comment in `Empty::take`.
        const { panic!("PerhapsKind::empty called on AlwaysKind") }
    }
}

impl<T: Send> Perhaps<T> for Always<T> {
    type Kind = Always<()>;

    fn just<R: Send>(f: impl FnOnce() -> R) -> Wrap<Self::Kind, R> {
        Always(f())
    }
    fn with<R: Send, E>(f: impl FnOnce() -> Result<R, E>) -> Result<Wrap<Self::Kind, R>, E> {
        Ok(Always(f()?))
    }
    fn take(self) -> T {
        self.0
    }
    fn map<U: Send, F>(self, f: F) -> Wrap<Self::Kind, U>
    where
        F: FnOnce(T) -> U,
    {
        Always(f(self.0))
    }
    fn into<U: Send>(self) -> Wrap<Self::Kind, U>
    where
        T: Into<U>,
    {
        Always(self.0.into())
    }
    fn clone(&self) -> Self
    where
        T: Clone,
    {
        Always(self.0.clone())
    }
    fn and_then<U: Send, F>(self, f: F) -> Wrap<Self::Kind, U>
    where
        F: FnOnce(T) -> Wrap<Self::Kind, U>,
    {
        f(self.0)
    }
    fn view(&self) -> Wrap<Self::Kind, &T>
    where
        T: Sync,
    {
        Always(&self.0)
    }
    fn view_mut(&mut self) -> Wrap<Self::Kind, &mut T> {
        Always(&mut self.0)
    }

    fn cast<R>(self) -> T::Output
    where
        T: PerhapsCast<R, Self::Kind>,
    {
        T::cast(self.0)
    }
}
