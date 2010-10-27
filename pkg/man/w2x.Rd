\name{w2x}
\alias{w2x}
\title{ From wealth time series to prices relative time series
}
\description{
  Transform a time series of wealths into a time series of prices
  relative of the same length.  Make sure that the first element is correct.
}
\usage{
w2x(w)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{w}{
    Time series of wealth.
  }
}
\details{
  Essentially perform w / lag(w) but add an initial value to keep the
  same length.
}
\value{
            Time series of relative prices
}
\author{ Marc Delvaux }
