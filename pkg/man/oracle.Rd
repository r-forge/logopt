\name{oracle}
\alias{oracle}
\title{ Show time evolution of absolute best possible portfoliobest }
\description{
  Time evolution of the portfolio of an oracle that can perfectly
  predict the time series of prices relative.
}
\usage{
oracle(x)
}
\arguments{
  \item{x}{
        Time series of relative prices
}
}
\details{
  Invest all current wealth on the best stock at any time index.  This
  gives an upperbound for the wealth of any portfolio selection algorithm.
}
\value{
  Time series of the wealth for the oracle portfolio.
}

\author{ Marc Delvaux}