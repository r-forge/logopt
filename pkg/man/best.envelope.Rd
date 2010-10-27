\name{best.envelope}
\alias{best.envelope}
\alias{worst.envelope}
\title{ Best or worst stock at any moment in time }
\description{
  Calculate the time evolution of all stocks based on the given prices
  relative and take the maximum or minimum at every time index.
}
\usage{
best.envelope(x)
}
\usage{
worst.envelope(x)
}
\arguments{
  \item{x}{
        Time series of relative prices
}
}
\details{
  Contrast to best.stock or worst.stock that shows the time evolution
  for the stock with the best or worst terminal wealth respectively.
}
\value{
  Time series of the best or worst wealth at any time index.
}
\author{ Marc Delvaux }
